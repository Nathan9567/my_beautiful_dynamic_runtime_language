package fr.umlv.smalljs.astinterp;

import fr.umlv.smalljs.ast.Expr;
import fr.umlv.smalljs.ast.Expr.Block;
import fr.umlv.smalljs.ast.Expr.Call;
import fr.umlv.smalljs.ast.Expr.FieldAccess;
import fr.umlv.smalljs.ast.Expr.FieldAssignment;
import fr.umlv.smalljs.ast.Expr.Fun;
import fr.umlv.smalljs.ast.Expr.Identifier;
import fr.umlv.smalljs.ast.Expr.If;
import fr.umlv.smalljs.ast.Expr.Literal;
import fr.umlv.smalljs.ast.Expr.MethodCall;
import fr.umlv.smalljs.ast.Expr.ObjectLiteral;
import fr.umlv.smalljs.ast.Expr.Return;
import fr.umlv.smalljs.ast.Expr.VarAssignment;
import fr.umlv.smalljs.ast.Script;
import fr.umlv.smalljs.rt.Failure;
import fr.umlv.smalljs.rt.JSObject;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static fr.umlv.smalljs.rt.JSObject.UNDEFINED;
import static java.util.stream.Collectors.joining;

public final class ASTInterpreter {
  private static JSObject asJSObject(Object value, int lineNumber) {
    if (!(value instanceof JSObject jsObject)) {
      throw new Failure("at line " + lineNumber + ", type error " + value + " is not a JSObject");
    }
    return jsObject;
  }

  private static Object execute(Expr.Block body, JSObject env) {
    // initialize declared variables to UNDEFINED
    visitVariable(body, env);
    // interpret the AST
    return visit(body, env);
  }

  private static void visitVariable(Expr expression, JSObject env) {
    switch (expression) {
      case Block(List<Expr> exprs, _) -> {
        for (var expr : exprs) {
          visitVariable(expr, env);
        }
      }
      case VarAssignment(String name, _, boolean declaration, _) -> {
        if (declaration) {
          env.register(name, UNDEFINED);
        }
      }
      case If(_, Block trueBlock, Block falseBlock, _) -> {
        visitVariable(trueBlock, env);
        visitVariable(falseBlock, env);
      }
      case Literal _, Call _, Identifier _, Fun _, Return _, ObjectLiteral _, FieldAccess _,
           FieldAssignment _, MethodCall _ -> {
        // do nothing
      }
    };
  }

  static Object visit(Expr expression, JSObject env) {
    return switch (expression) {
      case Block(List<Expr> exprs, _) -> {
        for (var expr : exprs) {
          visit(expr, env);
        }
        yield UNDEFINED;
      }
      case Literal(Object value, _) -> value;
      case Call(Expr qualifier, List<Expr> args, int lineNumber) -> {
        var value = visit(qualifier, env);
        if (!(value instanceof JSObject function)) {
          throw new Failure(value + " is not callable at line " + lineNumber);
        }
        yield function.invoke(UNDEFINED,
            args.stream().map(arg -> visit(arg, env)).toArray());
      }
      case Identifier(String name, int lineNumber) -> {
        var value = env.lookupOrDefault(name, null);
        if (value == null) {
          throw new Failure(name + " is not defined at line " + lineNumber);
        }
        yield value;
      }
      case VarAssignment(String name, Expr expr, boolean declaration, int lineNumber) -> {
        var value = visit(expr, env);
        if (!declaration && env.lookupOrDefault(name, null) == null) {
          throw new Failure(name + " is not defined at line " + lineNumber);
        }
        env.register(name, value);
        yield value;
      }
      case Fun(String name, List<String> parameters, boolean toplevel, Block body, int lineNumber) -> {
        JSObject.Invoker invoker = new JSObject.Invoker() {
          @Override
          public Object invoke(Object receiver, Object... args) {
            // check the arguments length
            if (args.length != parameters.size()) {
              throw new Failure("function " + name + " expected " + parameters.size() +
                  " arguments but got " + args.length + " at line " + lineNumber);
            }
            // create a new environment
            var localEnv = JSObject.newEnv(env);
            // add this and all the parameters
            localEnv.register("this", receiver);
            IntStream.range(0, parameters.size()).forEach(i ->
                localEnv.register(parameters.get(i), args[i])
            );
            // execute the body
            try {
              execute(body, localEnv);
            } catch (ReturnError re) {
              return re.getValue();
            }
            return UNDEFINED;
          }
        };

        // create the JS function with the invoker
        var function = JSObject.newFunction(name, invoker);
        // register it into the global env if it's a toplevel
        if (toplevel) {
          env.register(name, function);
        }
        // yield the function
        yield function;
      }
      case Return(Expr expr, _) -> {
        var value = visit(expr, env);
        throw new ReturnError(value);
      }
      case If(Expr condition, Block trueBlock, Block falseBlock, _) -> {
				var value = visit(condition, env);
        var isFalse = switch (value) {
          case Integer intValue -> intValue == 0;
          case String strValue -> strValue.isEmpty();
          default -> value == UNDEFINED;
        };
        if (!isFalse) {
          visit(trueBlock, env);
        } else {
          visit(falseBlock, env);
        }
        yield UNDEFINED;
      }
      case ObjectLiteral(Map<String, Expr> initMap, _) -> {
        var obj = JSObject.newObject(null);
        initMap.forEach((k, v) -> obj.register(k, visit(v, env)));
        yield obj;
      }
      case FieldAccess(Expr receiver, String name, int lineNumber) -> {
        var value = visit(receiver, env);
        if (!(value instanceof JSObject jsObject)) {
          throw new Failure("at line " + lineNumber + ", type error " + value + " is not a JSObject");
        }
        var fieldValue = jsObject.lookupOrDefault(name, null);
        if (fieldValue == null) {
          yield UNDEFINED;
        }
        yield fieldValue;
      }
      case FieldAssignment(Expr receiver, String name, Expr expr, int lineNumber) -> {
        var value = visit(receiver, env);
        if (!(value instanceof JSObject jsObject)) {
          throw new Failure("at line " + lineNumber + ", type error " + value + " is not a JSObject");
        }
        var fieldValue = visit(expr, env);
        jsObject.register(name, fieldValue);
        yield fieldValue;
      }
      case MethodCall(Expr receiver, String name, List<Expr> args, int lineNumber) -> {
        var obj = visit(receiver, env);
        if (!(obj instanceof JSObject jsObject)) {
          throw new Failure("at line " + lineNumber + ", type error " + obj + " is not a JSObject");
        }
        var method = jsObject.lookupOrDefault(name, null);
        if (!(method instanceof JSObject jsFunction)) {
          throw new Failure("at line " + lineNumber + ", type error " + method + " is not a JSObject");
        }
        yield jsFunction.invoke(jsObject,
            args.stream().map(arg -> visit(arg, env)).toArray());
      }
    };
  }

  @SuppressWarnings("unchecked")
  private static JSObject createGlobalEnv(PrintStream outStream) {
    var globalEnv = JSObject.newEnv(null);
    globalEnv.register("globalThis", globalEnv);
    globalEnv.register("print", JSObject.newFunction("print", (_, args) -> {
      System.err.println("print called with " + Arrays.toString(args));
      outStream.println(Arrays.stream(args).map(Object::toString).collect(Collectors.joining(" ")));
      return UNDEFINED;
    }));
    globalEnv.register("+", JSObject.newFunction("+", (_, args) -> (Integer) args[0] + (Integer) args[1]));
    globalEnv.register("-", JSObject.newFunction("-", (_, args) -> (Integer) args[0] - (Integer) args[1]));
    globalEnv.register("/", JSObject.newFunction("/", (_, args) -> (Integer) args[0] / (Integer) args[1]));
    globalEnv.register("*", JSObject.newFunction("*", (_, args) -> (Integer) args[0] * (Integer) args[1]));
    globalEnv.register("%", JSObject.newFunction("%", (_, args) -> (Integer) args[0] % (Integer) args[1]));
    globalEnv.register("==", JSObject.newFunction("==", (_, args) -> args[0].equals(args[1]) ? 1 : 0));
    globalEnv.register("!=", JSObject.newFunction("!=", (_, args) -> !args[0].equals(args[1]) ? 1 : 0));
    globalEnv.register("<", JSObject.newFunction("<", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) < 0) ? 1 : 0));
    globalEnv.register("<=", JSObject.newFunction("<=", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) <= 0) ? 1 : 0));
    globalEnv.register(">", JSObject.newFunction(">", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) > 0) ? 1 : 0));
    globalEnv.register(">=", JSObject.newFunction(">=", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) >= 0) ? 1 : 0));
    return globalEnv;
  }

  public static void interpret(Script script, PrintStream outStream) {
    var globalEnv = createGlobalEnv(outStream);
    var body = script.body();
    execute(body, globalEnv);
  }
}

