// Synthesized 
/**
	* OAuth.als
	* 
	* A model of OAuth 2.0
	* Based on the OAuth spec: http://tools.ietf.org/html/rfc6749
	* Protocol mode: Authorization code grant
	*/
module OAuth

open HTTP

fun composedWith : Proc -> Proc {
	MyApp -> ClientServer +
	Google -> AuthHTTPServer +
	Alice -> AliceBrowser +
	Eve -> EvilServer
}

fun knows : Proc -> Data -> Event {
	{ p : Proc, d : Data, e : Event |
		d in (p + composedWith[p]).owns or
		some e' : e.prevs |
			(d in e'.args and p in e'.receiver) or
			(d in e'.rets and p in e'.sender)
	}
}

/**
	*  OAuth-related datatypes
	*/
abstract sig OAuthID extends Data {}
abstract sig Token extends Data {}
abstract sig Resource extends Data {}
abstract sig AuthCode extends Token {}		// authorization grant
abstract sig UserCred extends Token {}		
abstract sig AccessToken extends Token {}	// access token

one sig id_Alice, id_Eve extends OAuthID {}
one sig AliceRes, EveRes extends Resource {}
one sig code_Alice, code_Eve extends AuthCode {}
one sig cred_Alice, cred_Eve extends UserCred {}
one sig token_Alice, token_Eve extends AccessToken {}

/**
* Abstract labels
*/

-- auxiliary stuff
fun OAuthModules : set Module {
	AuthServer + Client + UserAgent
}
fun OAuthData : set Data {
	Token + Resource + OAuthID + Session
}
fun OAuthLabel : set Event {
	authorize + forward + getAccessToken + initiate + OtherOp
}

/**
	* Participanting components
	*/
// Authorization server, which grants OAuthClient access to a resource. 
abstract sig AuthServer extends Module {
	tokens : AuthCode -> AccessToken,
	codes : UserCred -> AuthCode,
	creds : OAuthID -> lone UserCred,
	owner : Resource -> lone OAuthID,
	// maps each resource to the access token that it protects
	resACL : Resource -> AccessToken,
}

// Client requesting access to a resource 
abstract sig Client extends Module {}

// User/owner of a resource
abstract sig UserAgent extends Module {
	id : OAuthID,
	cred : UserCred
}

/**
	* Operations that represent different steps of the OAuth protocol
	*/

// 1. Authentication step
// from UserAgent to AuthServer
// AuthServer authenticates the user and
// returns a corresponding authorization code
sig authorize extends DataflowLabel {
	userid : OAuthID,
	cred : UserCred,
	code : AuthCode	
}{
	args & OAuthData = cred + userid
	rets & OAuthData = code
	some UserAgent & sender 
	some AuthServer & receiver
}

// 2. Pass auth code
// from UserAgent to OAuthClient
// User passes the authorization code to the client
abstract sig forward extends DataflowLabel {
	code : AuthCode
}

// 3. Requesting access token
// from OAuthClient to AuthServer
// The client sends the authorization code directly to the auth server
// to receive an access token
sig getAccessToken extends DataflowLabel {
	code : AuthCode,
	token : AccessToken
}{
	args & OAuthData = code
	rets & OAuthData = token
	some sender & Client 
	some receiver & AuthServer
}

sig OtherOp extends DataflowLabel {}{	
	some sender & AliceBrowser
	some receiver & EvilServer
	this not in RedirectReq 
		implies no args & (UserCred + AuthCode + Session + NONCE)
}

-------------

/** 
	* Instantiation 
	*/
one sig Alice extends UserAgent {}{
	id = id_Alice
	cred = cred_Alice
	owns = cred + id_Alice
	
	// user behavior
	all e : Event & sender.this |
		e in ForwardToMyApp implies e in RedirectReq		
}

one sig Eve extends UserAgent {}{
	id = id_Eve
	cred = cred_Eve
	owns = cred + id_Eve
}
one sig MyApp extends Client {}{
	owns = Session
}

pred myApp_sessions[e : Event, i : Session, u : UserAgent] {
	some e' : e.prevs & procs.MyApp & initiate |
		u in e'.sender and i = e'.session
}

pred myApp_codes[e : Event, i : Session, c : AuthCode] {
	some e' : e.prevs & procs.MyApp, l : e' & ForwardToMyApp |
			i = l.session and c = l.code	
}

pred myApp_tokens[e : Event, i : Session, t : AccessToken] {
	some e' : e.prevs & procs.MyApp, l : e' & getAccessToken |
		t = l.token and
		myApp_codes[e', i, l.code] 
}

// App related datatypes and 
abstract sig Session extends Data {}
one sig session_X extends Session {}
one sig session_Y extends Session {}


sig initiate extends DataflowLabel {
	session : Session
}{
	no args & OAuthData
	rets & OAuthData = session
	some sender & UserAgent 
	some receiver & MyApp
}
sig ForwardToMyApp extends forward {
	session : Session
}{
	args & OAuthData = session + code
	no rets & OAuthData
	some sender & UserAgent 
	some receiver & MyApp
}

one sig Google extends AuthServer {}{
	tokens = code_Alice -> token_Alice + code_Eve -> token_Eve
	codes = cred_Alice -> code_Alice + cred_Eve -> code_Eve
	creds = id_Alice -> cred_Alice + id_Eve -> cred_Eve
	owner = AliceRes -> id_Alice + EveRes -> id_Eve
	resACL = AliceRes -> token_Alice + EveRes -> token_Eve
	owns = AuthCode + AccessToken + UserCred + Resource
}

fun Trusted : set Module {
	Alice + MyApp + Google
}

/**
	HTTP instantiations
*/
one sig AuthHTTPServer extends Server {}{
	host = HostGoogle
	owns in Google.@owns + NONCE
}
fun port_auth_server : set HTTPReq {
	HTTPReq & receiver.AuthHTTPServer
}

one sig ClientServer extends Server {}{
	host = HostMyApp
	owns in MyApp.@owns + NONCE
}
fun port_client : set HTTPReq {
	HTTPReq & receiver.ClientServer
}

one sig EvilServer extends Server {}{
	host = HostEvil
	owns in Eve.@owns
}
one sig AliceBrowser extends Browser {}{
	no addr
	owns in Alice.@owns
}

fun alpha : Proc -> Event {
	UserAgent -> (authorize + forward + initiate) + 
	Client -> (forward + getAccessToken + initiate) + 
	AuthServer -> (authorize + getAccessToken) + 
	OAuthModules -> OtherOp +
	// from HTTP
	Browser -> HTTPReq + 
	Server -> HTTPReq 
}

one sig path_authorize,path_initiate,path_forward,
path_evilPage,path_getAccessToken extends Path {}

one sig ORIGIN_MYAPP extends Origin {}{ host = HostMyApp }
one sig ORIGIN_GOOGLE extends Origin {}{ host = HostGoogle }
one sig ORIGIN_ATTACKER extends Origin {}{ host = HostEvil }
one sig HostMyApp, HostGoogle, HostEvil extends Host {}
abstract sig NONCE extends Data {}
one sig NONCE0,NONCE1,NONCE3 extends NONCE {}

one sig HTML1 extends HTML {}
one sig HTML2 extends HTML {}
one sig HTML3 extends HTML {}
one sig HTML4 extends HTML {}
one sig HTML5 extends HTML {}

/**
	* Behavior definitions
	*/

// Behaviors of individual processes
pred processBehavior {
	// General dataflow behavior
	all e : Event, p : Proc |	
		(p in e.sender implies e.args in p.knows.e) and
		(p in e.receiver implies e.rets in e.args + p.knows.e)
	processBehavior_OAuth
	processBehavior_HTTP
}

pred systemBehavior {
	all e : Event {		
		all p : e.procs | some e & alpha[p]
		one e.sender & OAuthModules
		one e.receiver & OAuthModules 
		one e.sender & (Browser + Server) 
		one e.receiver & (Browser + Server)
	}
	all e : Event, p : e.sender | composedWith[p] in e.sender
	all e : Event, p : e.receiver | composedWith[p] in e.receiver
	processBehavior
}

// OAuth protocol behavior
pred processBehavior_OAuth {
	// User agent behavior
	all o : authorize, u : o.procs & UserAgent & Trusted {
		o.userid = u.id and o.cred = u.cred
	}

	// AuthServer behavior
	all o : authorize, s : o.procs & AuthServer & Trusted {
		o.userid -> o.cred in s.creds
		// AuthReq must provide a OAuth user credential that corresponds to
		// the authorization grant returned 	
		o.cred -> o.code in s.codes
	}

	all o : getAccessToken, s : o.procs & AuthServer & Trusted {
		// AccessTokenReq must provide an authorization grant that corresponds to
		// the access token returned
		o.code -> o.token in s.tokens
	}

	// MyApp behavior
	all o : initiate & procs.MyApp {
		all o' : o.prevs & procs.MyApp & initiate {
			o.session != o'.session
		}
	}
		
	all f : ForwardToMyApp & procs.MyApp {
		some o : f.prevs & procs.MyApp & initiate {
			o.session = f.session
		}
	}
}

// HTTP process behavior
pred processBehavior_HTTP {
	/**
	HTTP servers
	*/
	// only accepts requests with the same host as the server
	all s : Server, r : HTTPReq {
		s in r.receiver implies {
			r.url_origin.host = s.host
			// return the cookie with the right origin
			all c : Cookie | c in r.resp_set_cookie implies c.origin = r.url_origin
		}
	}

	/**
	Browser
	*/
	// behavior of the browser with respect to how it handles cookies
	all b : Browser, r : HTTPReq {
		b in r.sender implies {
			all c :  r.cookie {
				// Every cookie included in this request matches the origin of the request URL
				c.origin = r.url_origin
				// There must have been a set-cookie header received as part of a previous request
				some r' : r.prevs & procs.b & HTTPReq |
					c in r'.resp_set_cookie and c.origin = c.set_origin				
			}
		}
	}

	// behavior of the browser with respect to how it handles HTTP requests
	all b : Browser, r : RedirectReq {
		b in r.sender implies
			some r' : r.prev & procs.b & HTTPReq  |
				r' = r.trigger and
				r.url_origin in r'.resp_redirectTo_origin and
				r.url_path in r'.resp_redirectTo_path and
				no r.body and 
				r.(url_query + url_query2) in r'.(resp_redirectTo_query + resp_redirectTo_query2)
	}
}

/**
	Properties
*/

pred oauthProperty {
	// Integrity: Eve's token should not be associated with Alice's account
	// This will allow Eve's to access Alice's account
	all e : Event, id : Session |
		myApp_tokens[e, id, token_Eve] implies	
			not myApp_sessions[e, id, Alice]
}

pred oauthProperty2 {
	// Similar to oauthPropert1
	// Alice's token should not be associated with Eve's account
	// This may be used by Eve to trick Alice into log into Eve's account and store data
	all e : Event, id : Session |
		myApp_tokens[e, id, token_Alice] implies	
			not myApp_sessions[e, id, Eve]
}

fun procs : Event -> Proc {
	{e : Event, p : Proc | p in e.(sender + receiver) }
}

// Some sample scenarios to use as test cases
// to ensure that the mappings aren't overconstrained
// i.e., the resulting implementation allows some "good" behaviors
pred scenario1 {
	// Alice can complete the OAuth protocol and obtain an access token
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Alice] 
		and Alice -> id -> e in knows
}
pred scenario2 {
	// Eve can complete the OAuth protocol and obtain an access token
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Eve] 
		and Eve -> id -> e in knows
}
pred scenario3 {
	// A malicious server can accept HTTP requests
	some r : HTTPReq | 
		EvilServer in r.receiver
}


run scenario1Check { systemBehavior and partialConstraints and scenario1 } for 1 but 3 Event
run scenario2Check { systemBehavior and partialConstraints and scenario2 } for 6 but 8 Event
run scenario3Check { systemBehavior and partialConstraints and scenario3 } for 6 but 8 Event
run AllScenarios { systemBehavior and partialConstraints and scenario1 and scenario2 and scenario3 } for 6 but 8 Event

/**
	* Mapping constraints
	*/

// User-specified partial mapping constraints
pred partialConstraints {
	all o : OAuthLabel | o in HTTPReq
	
	all i : initiate | let r = i { 
		r in GET
		r.url_path = path_initiate
		// sessions are stored as cookies	
		r.resp_set_cookie = i.session
		i.session in SetCookie
	}
	all a : authorize | let r = a {
		r.url_path = path_authorize	
		r in POST
		r.resp_redirectTo_origin = ORIGIN_MYAPP
		some r.receiver & AuthHTTPServer
	}
	all f : forward | let r = f {
		r.url_path = path_forward	
		r in POST
	}
	all g : getAccessToken | let r = g {
		r.url_path = path_getAccessToken
		r in GET
		// code is transmitted as a query
		r.url_query = g.code
		// token is returned in the response body
		r.resp_resource.content = g.token
	}	
}

check goodMapping {
	systemBehavior and
	partialConstraints and 
	synthesizedConstraints_Good 
		implies oauthProperty
} for 6 but 8 Event

check badMapping {
	systemBehavior and 
	partialConstraints and
	synthesizedConstraints_Bad
		implies oauthProperty
} for 6 but 8 Event

// Synthesized mapping constraints
pred synthesizedConstraints_Good {
  // mapping from authorize to port_auth_server
  all a : authorize | let b = a { b in port_auth_server
    no b.resp_resource.content
    no b.cookie
    b.url_query = a.userid
    no b.resp_set_cookie
    b.resp_code = REDIRECT
    b.resp_redirectTo_query = a.code
    b.url_origin = ORIGIN_GOOGLE
    b.resp_redirectTo_origin = ORIGIN_MYAPP
    b.resp_redirectTo_path = path_forward
    b.resp_redirectTo_query2 = a.body
    b.url_path = path_authorize
    b.url_query2 = a.cred
  }
  // mapping from initiate to port_client
  all a : initiate | let b = a { b in port_client
    (b.resp_set_cookie = session_X) implies b.resp_resource.content = NONCE0
    (b.resp_set_cookie = session_Y) implies b.resp_resource.content = NONCE1
    no b.cookie
    no b.url_query
    b.resp_set_cookie = a.session
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_initiate
    no b.url_query2
  }
  // mapping from forward to port_client
  all a : forward | let b = a { b in port_client
    no b.resp_resource.content
    b.cookie = a.session
    b.url_query = a.code
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_forward
    (b.cookie = session_X) implies b.url_query2 = NONCE0
    (b.cookie = session_Y) implies b.url_query2 = NONCE1
  }
  // mapping from getAccessToken to port_auth_server
  all a : getAccessToken | let b = a { b in port_auth_server
    b.resp_resource.content = a.token
    no b.cookie
    b.url_query = a.code
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_getAccessToken
    no b.url_query2
  }
}

pred synthesizedConstraints_Bad {
// mapping from getAccessToken to port_auth_server
  all a : getAccessToken | let b = a { b in port_auth_server
    b.resp_resource.content = a.token
    b.url_query = a.code
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_getAccessToken
    no b.url_query2
  }
  // mapping from forward to port_client
  all a : forward | let b = a { b in port_client
    no b.resp_resource.content
    b.cookie = a.session
    b.url_query = a.code
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.resp_redirectTo_query2
    b.url_path = path_forward
    no b.url_query2
  }
  // mapping from Authorize to port_auth_server
  all a : authorize | let b = a { b in port_auth_server
    no b.resp_resource.content
    no b.cookie
    b.url_query = a.userid
    no b.resp_set_cookie
    b.resp_code = REDIRECT
    b.resp_redirectTo_query = a.code
    b.url_origin = ORIGIN_GOOGLE
    b.resp_redirectTo_origin = ORIGIN_MYAPP
    b.resp_redirectTo_path = path_forward
    b.body = a.cred
    no b.resp_redirectTo_query2
    b.url_path = path_authorize
    no b.url_query2
  }
  // mapping from initiate to port_client
  all a : initiate | let b = a { b in port_client
    no b.resp_resource.content
    no b.cookie
    no b.url_query
    b.resp_set_cookie = a.session
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_initiate
    no b.url_query2
  }
}

