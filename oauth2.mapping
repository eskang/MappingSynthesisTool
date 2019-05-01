// abstract and concrete labels
val authorize = Store.l("authorize")
val forward = Store.l("forward")
val initiate = Store.l("initiate")
val getAccessToken = Store.l("getAccessToken")
val authServerPort = Store.l("port_auth_server")
val clientPort = Store.l("port_client")

// Abstract-concrete label pairs,
// each along with user-defined constraints
val i2h = new ImplConstraints(initiate, clientPort)

i2h.addEqualConstraints(
  Map(
    "req.url.path" -> "path_initiate",
    "req.url.origin" -> "ORIGIN_MYAPP",
    "req.cookie" -> "none",
    "req.body" -> "none",
    "req.url.query" -> "none",
    "req.url.query2" -> "none",
    "resp.redirectTo.path" -> "none",
    "resp.redirectTo.origin" -> "none",
    "resp.redirectTo.query" -> "none",
    "resp.redirectTo.query2" -> "none",
    //"resp.resource.content" -> "$COND_FUNC(resp.set_cookie,session)",
    "resp.set_cookie" -> "session",
    "resp.code" -> "OK"))

val a2h = new ImplConstraints(authorize, authServerPort)
a2h.addEqualConstraints(
  Map(
    "req.url.path" -> "path_authorize",
    "req.url.query" -> "userid",
    //"req.url.query2" -> "some",
    "req.url.origin" -> "ORIGIN_GOOGLE",
    "resp.code" -> "REDIRECT",
    "resp.set_cookie" -> "none",
    "req.cookie" -> "none",
    //"req.body" -> "cred",
    //"resp.resource.content" -> "none",
    "resp.redirectTo.path" -> "path_forward",
    "resp.redirectTo.origin" -> "ORIGIN_MYAPP",
    "resp.redirectTo.query" -> "code"))

val f2h = new ImplConstraints(forward, clientPort)
f2h.addEqualConstraints(
  Map(
    "req.url.path" -> "path_forward",
    "req.url.query" -> "code",
    "req.cookie" -> "session",
    "req.url.origin" -> "ORIGIN_MYAPP",
    "resp.code" -> "OK",
    "resp.redirectTo.path" -> "none",
    "resp.redirectTo.origin" -> "none",
    "resp.redirectTo.query" -> "none",
    "resp.redirectTo.query2" -> "none",
    "resp.resource.content" -> "none",
    //"req.url.query2" -> "$COND_FUNC(req.cookie,session)",
    "resp.set_cookie" -> "none"))

val g2h = new ImplConstraints(getAccessToken, authServerPort)
g2h.addEqualConstraints(
  Map(
    "req.url.path" -> "path_getAccessToken",
    "req.url.query" -> "code",
    "req.url.query2" -> "none",
    "req.url.origin" -> "ORIGIN_GOOGLE",
    "resp.code" -> "OK",
    "req.body" -> "none",
    "req.cookie" -> "none",
    "resp.set_cookie" -> "none",
    "resp.resource.content" -> "token",
    "resp.redirectTo.path" -> "none",
    "resp.redirectTo.origin" -> "none",
    "resp.redirectTo.query" -> "none",
    "resp.redirectTo.query2" -> "none"))
MappingFactory.mkMapping(Set(a2h, i2h, f2h, g2h))
 