int test = 1;

typedef mixed sexp;
typedef string symbol;
typedef array(sexp) list;
// no bools here; empty list is our false value, all else being true. 

class env {
  array(mapping(sexp:sexp)) contents = ({ ([]) });

  int has_internal(array e, sexp k) {
    if (sizeof(e) == 0) return 0;
    if (!zero_type(e[0][k])) return 1;
    return has_internal(e[1..], k);
  }

  int has(sexp k) {
    return has_internal(contents, k);
  }

  sexp get_internal(array e, sexp k) {
    if (sizeof(e) == 0) die("Not found: ", k);
    if (!zero_type(e[0][k])) return e[0][k];
    return has_internal(e[1..], k);
  }

  sexp get(sexp k) {
    return get_internal(contents, k);
  }

  sexp `[](sexp k) {
    return get(k);
  }

  void set_internal(array e, sexp k, sexp v) {
    if (sizeof(e) == 0) die("Not found: ", k);
    if (!zero_type(e[0][k])) 
      e[0][k] = v;
    else
      set_internal(e[1..], k, v);
  }
    
  void set(sexp k, sexp v) {
    set_internal(contents, k, v);
  }

  sexp `[]=(sexp k, sexp v) {
    set(k, v);
  }

  env extend(array params, array args) {
    mapping newc = ([]);
    array bindings = zip(params, args);
    map(bindings, lambda(array b) {
      newc[b[0]] = b[1];
    });
    array newcontents = ({ newc }) + contents;
    env newenv;
    newenv->contents = newcontents;
    return newenv;
  }
}

env global_env = env();

void die(string err, mixed e) {
  error(err + to_string(e) + "\n");
  exit(1);
}

string to_string(mixed x) {
  if (stringp(x) || intp(x) || floatp(x)) return x;
  if (arrayp(x)) {
    x = map(x, to_string);
    return "(" + (x * ", ") + ")";
  }
  if (mappingp(x)) {
    x = map(indices(x), lambda(mixed k) {
      return to_string(k) + " => " + to_string(x[k]);
    });
    return "{" + (x * ", ") + "}";
  }
  if (multisetp(x)) return "<multiset>";
  if (programp(x)) return "<program>";
  if (objectp(x)) return "<object>";
  if (functionp(x)) return "<Pike function " + function_name(x) + ">";
}

mixed foldl(function f, mixed z, array x) {
  if (equal(x, ({}) )) return z;
  return foldl(f, f(z, x[0]), x[1..]);
}

sexp env_lookup(env c, sexp e) {
  if (!zero_type(c[e]))
    return c[e];
  if (!zero_type(global_env[e]))
    return global_env[e];
  die("Not found in environment: ", e);
}

void set_env(env c, sexp k, sexp v) {
  if (!zero_type(c[k])) 
    c[k] = v;
  else if (!zero_type(global_env[k]))
    global_env[k] = v;
  die("Not found in environment for set: ", k);
}

array zip(array x, array y) {
  if (sizeof(x) == 0 || sizeof(y) == 0)
    return ({});
  return ({ ({x[0], y[0]}) }) + zip(x[1..], y[1..]);
}

function evalc(env c) {
  return lambda(sexp e) {
    return eval(c, e);
  };
}

sexp eval(env c, sexp e) {
  if (intp(e)) return e; 
  else if (stringp(e)) return env_lookup(c, e);
  else if (equal(e, ({}) )) return e;
  else if (arrayp(e)) {
    sexp head = e[0];
    array tail = e[1..];
    switch(head) {
      case "progn":
        if(sizeof(tail) == 0) return ({});
        array results = map(tail, evalc(c));
        return results[-1];
      case "quote":
        if(sizeof(tail) != 1) die("Quote applied to other than one arg in exp: ", e);
        return tail[0];
      case "lamba":
        if(!arrayp(tail[0])) die("Lambda arglist not array in exp: ", e);
        array params = tail[0];
        array body = ({ "progn" }) + tail[1..];
        return lambda (array args) {
          env newc = c.extend(params, args);
          return eval(newc, body);
        };
      case "define":
        sexp name;
        sexp value;
        if (stringp(tail[0])) {
          if (sizeof(tail) != 2) die("Define of symbol with other than one value in exp: ", e);
          name = tail[0];
          value = tail[1];
        } else if (arrayp(tail[0])) {
          if (sizeof(tail[0]) == 0) die("Define of nil: ", e);
          name = tail[0][0];
          array params = tail[0][1..];
          array body = ({ "progn" }) + tail[1..];
          value = lambda (array args) {
            env newc = c.extend(params, args);
            return eval(newc, body);
          };
        } else {
          die("Bad define: ", e);
        }
        global_env[name] = value;
        return value;
      case "setq":
        if (sizeof(tail) != 2) die("Setq applied to other than two args in exp: ", e);
        sexp val = eval(c, tail[1]);
        set_env(c, tail[0], val);
        return val;
      default:
        die("No case of eval for: ", e);
        break;
    }
  } else {
    die("No case of eval for: ", e);
  }
}

void main() {
}
