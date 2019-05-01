/**
	* OAuth.als
	* 
	* A model of OAuth
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
	authorize + forward + getAccessToken + initiate + OtherOp //+ ReadResource + GetResource 
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

// 4. Request resource
// A request for a resource on ResServer
/*
abstract sig GetResource extends DataflowLabel {
	token : AccessToken,
	res : Resource
}{
	args = token
	rets = res 
}
*/

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

/*
fun myApp_resources[procs : Event -> Proc, labels : Event -> Label] : Event -> Session -> Resource {
	{ e : Event, i : Session, r : Resource |
		some e' : e.prevs & procs.MyApp, l : e'.labels & GetResource |
			r = l.res and
			e' -> i -> l.token in myApp_tokens[procs, labels]
	}
}
*/

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

/*
abstract sig ReadResource extends DataflowLabel {
	appID : Session,
	res : Resource
}{
	args = appID 
	rets = res
}
*/

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
//one sig EveBrowser extends Browser {}{ no addr }

fun alpha : Proc -> Event {
	UserAgent -> (authorize + forward + initiate) + // + ReadResource) + 
	Client -> (forward + getAccessToken + initiate) + // + GetResource +  + ReadResource) + 
	AuthServer -> (authorize + getAccessToken) + // + GetResource)
	OAuthModules -> OtherOp +
	// from HTTP
	Browser -> HTTPReq + 
	Server -> HTTPReq 
}

one sig path_authorize,path_initiate,path_forward,
path_evilPage,path_getAccessToken extends Path {}

//one sig URLMyApp extends URL {}{ origin = ORIGIN_MYAPP }
//one sig URLGoogle extends URL {}{ origin = ORIGIN_GOOGLE }
//one sig URLEvilServer extends URL {}{ origin = ORIGIN_ATTACKER }
one sig ORIGIN_MYAPP extends Origin {}{ host = HostMyApp }
one sig ORIGIN_GOOGLE extends Origin {}{ host = HostGoogle }
one sig ORIGIN_ATTACKER extends Origin {}{ host = HostEvil }
one sig HostMyApp, HostGoogle, HostEvil extends Host {}

one sig HTML1 extends HTML {}
one sig HTML2 extends HTML {}
one sig HTML3 extends HTML {}
one sig HTML4 extends HTML {}
one sig HTML5 extends HTML {}

/**
	* Behaviors
	*/

pred assumptions {
}

pred userConstraint {
	// Every mapping should allow some behavior that is defined in "scenario"
	// This is to ensure that the mapping is not too restrictive
	all o : OAuthLabel | o in HTTPReq
/*
	all o : OAuthLabel & HTTPReq | let r = o | 
		(r.url_query + r.url_query2 + r.cookie + r.body) & (OAuthData + Session) in o.args and
		(r.resp_set_cookie + r.resp_resource.content + r.resp_redirectTo.(query + query2)) & (OAuthData + Session) in o.rets
*/
	all i : initiate | let r = i { 
		r.resp_set_cookie = i.session
		i.session in SetCookie
//		no r.resp_resource.content 
//		r.resp_redirectTo.origin = ORIGIN_GOOGLE
	}

	all a : authorize | let r = a {		
		r.(resp_redirectTo_query + resp_redirectTo_query2) & AuthCode = a.code
		r.resp_redirectTo_origin = ORIGIN_MYAPP
		some r.receiver & AuthHTTPServer
	}

	all f : forward | let r = f {
		f.session in r.cookie & Cookie	
//		no r.resp_redirectTo
	}

/*	
	all f : forward | let r = f {
		some r.(url_query + url_query2) & Hash implies
			some i : initiate | let r' = i |
				r.(url_query + url_query2) & Hash in r'.(resp_redirectTo_query + resp_redirectTo_query2)
	}

	all a : authorize | let r = a {
		some r.(url_query + url_query2) & Hash implies
			some i : initiate | let r' = i  |
				r.(url_query + url_query2) & Hash in r'.(resp_redirectTo_query + resp_redirectTo_query2)	
	}
*/
}

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
/*
	all e : Event, o : GetResource, s : e.procs & AuthServer & Trusted {
		e -> o in labels implies {
			o.res -> o.token in s.resACL
		}
	}	
*/
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

/*
	all e : procs.MyApp, o : ReadResource {
		e -> o in labels implies
			e -> o.session -> o.res in myApp_resources[procs, labels]
	}
*/

}

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
	Property 
*/

pred oauthProperty {
/*
	all e : Event, r : ReadResource |
		e -> r in labels and r.res = AliceRes implies
			Eve not in e.procs
*/
/*
	all e : Event, id : Session |
		myApp_tokens[procs, labels, e, id, token_Alice] implies	
			Eve -> e -> id not in knows[procs, labels]	
*/
	all e : Event, id : Session |
		myApp_tokens[e, id, token_Eve] implies	
			not myApp_sessions[e, id, Alice]
}

pred oauthProperty2 {
	all e : Event, id : Session |
		myApp_tokens[e, id, token_Alice] implies	
			not myApp_sessions[e, id, Eve]
}

pred processBehavior {
	// General dataflow behavior
	all e : Event, p : Proc |	
		(p in e.sender implies e.args in p.knows.e) and
		(p in e.receiver implies e.rets in e.args + p.knows.e)

	processBehavior_OAuth
	processBehavior_HTTP

/*
	all e : Event, s : Server, r : HTTPReq {
		// servers don't expose Alice's credential
		(e -> r in labels and e -> s in procs and s in receivers[procs,labels][e][r]) implies {
			cred_Alice not in r.rets
		}
	}
*/
}

fun procs : Event -> Proc {
	{e : Event, p : Proc | p in e.(sender + receiver) }
}

pred behavior {
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

/*
pred goodMapping[m : Label -> Label] {
	all procs : Event -> Proc, labels : Event -> Label |
		(applyMapping[m, procs, labels] and behavior[procs, labels]) implies
			oauthProperty[procs, labels]
}
*/

pred scenario1 {
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Alice] 
		and Alice -> id -> e in knows
}
pred scenario2 {
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Eve] 
		and Eve -> id -> e in knows
}
pred scenario3 {
	some r : HTTPReq | 
		EvilServer in r.receiver
}

pred test {}


pred mappingLiveness1 {
	userConstraint
	mappingConstraints
	behavior
	scenario1
//	scenario2
//	scenario3
}

pred mappingLiveness2 {
	userConstraint
	mappingConstraints
	behavior
//	scenario1
	scenario2
//	scenario3
}

pred mappingSafety {
	userConstraint
	mappingConstraints
	behavior
	not oauthProperty
}

abstract sig NONCE extends Data {}

/*
run checkTest {
	userConstraint
	testMapping2
	behavior
	not oauthProperty
//	not oauthProperty2
//	scenario1
//	scenario2
} for 4 but 8 Event//, 7 Step

pred mappingConstraints {}

one sig NONCE2, NONCE3 extends NONCE {}

pred testMapping1 {
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

pred testMapping2 {
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
    (b.cookie = session_X) implies b.url_query2 = NONCE2
    (b.cookie = session_Y) implies b.url_query2 = NONCE3
  }
  // mapping from Authorize to port_auth_server
  all a : authorize | let b = a { b in port_auth_server
    no b.resp_resource.content
    no b.cookie
    b.url_query = a.userid
 //   some b.url_query2
    no b.resp_set_cookie
    b.resp_code = REDIRECT
    b.resp_redirectTo_query = a.code
    b.url_origin = ORIGIN_GOOGLE
    b.resp_redirectTo_origin = ORIGIN_MYAPP
    b.resp_redirectTo_path = path_forward
    b.body = a.cred
    b.url_path = path_authorize
    b.resp_redirectTo_query2 = b.url_query2
   //(b.url_query = id_Alice) implies b.resp_redirectTo_query2 =NONCE2
   //(b.url_query = id_Eve) implies b.resp_redirectTo_query2 =NONCE3
  }
  // mapping from initiate to port_client
  all a : initiate | let b = a { b in port_client
    (b.resp_set_cookie = session_X) implies b.resp_resource.content = NONCE2
    (b.resp_set_cookie = session_Y) implies b.resp_resource.content = NONCE3    
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

pred testMapping2backup {
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
    (b.cookie = session_X) implies b.url_query2 = NONCE2
    (b.cookie = session_Y) implies b.url_query2 = NONCE3
  }
  // mapping from authorize to port_auth_server
  all a : authorize | let b = a { b in port_auth_server
    no b.resp_resource.content
    no b.cookie
    b.url_query = a.userid
    some 
	b.url_query2
    no b.resp_set_cookie
    b.resp_code = REDIRECT
    b.resp_redirectTo_query = a.code
    b.url_origin = ORIGIN_GOOGLE
    b.resp_redirectTo_origin = ORIGIN_MYAPP
    b.resp_redirectTo_path = path_forward
    b.body = a.cred
    b.url_path = path_authorize
    b.resp_redirectTo_query2 
	= b.url_query2
  }
  // mapping from initiate to port_client
  all a : initiate | let b = a { b in port_client
    (b.resp_set_cookie = session_X) implies b.resp_resource.content = NONCE2
    (b.resp_set_cookie = session_Y) implies b.resp_resource.content = NONCE3    
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
*/
run {
	userConstraint
	behavior
	scenario1
} for 4 but 6 Event

run { 
	userConstraint
	behavior
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Alice] 
		and Alice -> id -> e in knows
/*
	let e0 = first, e1 = first.next, e2 = e1.next {//, e3 = e2.next, e4 = e3.next {
		e0 in initiate & HTTPReq
		Alice in e0.sender	
		MyApp in e0.receiver
		e1 in authorize
		Alice in e1.sender
		Google in e1.receiver
		Alice -> (e1.rets & AuthCode) -> e2 in knows
		Alice -> (e0.rets & Session) -> e2 in knows
		e2 in ForwardToMyApp
	}
*/
	
//		not oauthProperty[procs, labels]
/*
		let e = first, e0 = first.next, e1 = e0.next, e2 = e1.next, e3 = e2.next, e4 = e3.next, 
			aliceInit = e.labels & initiate, 
			eveInit = e0.labels & initiate, eveAuth = e1.labels & authorize, aliceVisit = e2.labels & HTTPReq, 
			aliceForward = e3.labels & ForwardToMyApp, getToken = e4.labels & getAccessToken {
				// Step 0
				some aliceInit
				Alice + MyApp in e.procs
				// Step 1
				some eveInit
				Eve + MyApp in e0.procs 
				// Step 2
				some eveAuth
				Eve + Google in e1.procs
				code_Eve in eveAuth.rets			
				// Step 3
				some aliceVisit
				e2.procs = AliceBrowser + EvilServer
				code_Eve in aliceVisit.rets
				// Step 4
				some aliceForward				
				Alice + MyApp in e3.procs
				code_Eve = aliceForward.code
				// Step 5
				some getToken
				MyApp + Google in e4.procs
		}
*/

/*
		let e0 = first, e1 = e0.next, e2 = e1.next, e3 = e2.next,
			aliceInit = e0.labels & initiate, aliceAuth = e1.labels & authorize,  
			aliceForward = e2.labels & ForwardToMyApp, getToken = e3.labels & getAccessToken {
				// Step 1
				some aliceInit
				Alice + MyApp in e0.procs 
				// Step 2

				some aliceAuth
				Alice + Google in e1.procs
				code_Alice in aliceAuth.rets 
				some (aliceAuth.m).redirectTo
				//(aliceInit.m).responseHeaders & Hash in (aliceAuth.m).redirectTo.query
				// Step 3
				some aliceForward
				Alice + MyApp in e2.procs
				code_Alice = aliceForward.code
				// Step 4
				some getToken
				MyApp + Google in e3.procs
		}
*/

} for 5 

run attack { 
	userConstraint
	behavior
	not oauthProperty

/*
lone OtherOp
		let e = first, e0 = first.next, e1 = e0.next, e2 = e1.next, e3 = e2.next, e4 = e3.next, 
			aliceInit = e &  initiate, 
			eveInit = e0 & initiate, eveAuth = e1 & authorize, aliceVisit = e2 & HTTPReq, 
			aliceForward = e3 & ForwardToMyApp, getToken = e4 & getAccessToken {
				// Step 0
				some aliceInit
				Alice + MyApp in e.procs
				// Step 1
				some eveInit
				Eve + MyApp in e0.procs 
				// Step 2
				some eveAuth
				Eve + Google in e1.procs
				code_Eve in eveAuth.rets			
				// Step 3
				some aliceVisit
				Alice + AliceBrowser + Eve + EvilServer = e2.procs
				aliceVisit.resp_redirectTo_origin = ORIGIN_MYAPP
				aliceVisit.resp_redirectTo_path = path_forward
				code_Eve in aliceVisit.rets

				// Step 4
				some aliceForward		
				Alice + MyApp in e3.procs
				Alice -> code_Eve -> e3 in knows
				code_Eve = aliceForward.code
				// Step 5
				some getToken
				MyApp + Google in e4.procs

		}
*/
/*
		let e0 = first, e1 = e0.next, e2 = e1.next, e3 = e2.next,
			aliceInit = e0.labels & initiate, aliceAuth = e1.labels & authorize,  
			aliceForward = e2.labels & ForwardToMyApp, getToken = e3.labels & getAccessToken {
				// Step 1
				some aliceInit
				Alice + MyApp in e0.procs 
				// Step 2
				some aliceAuth
				Alice + Google in e1.procs
				code_Alice in aliceAuth.rets 
				some (aliceAuth.m).redirectTo
//				(aliceInit.m).responseHeaders & Hash in (aliceAuth.m).redirectTo.query
				// Step 3
				some aliceForward
				Alice + MyApp in e2.procs
				code_Alice = aliceForward.code
				// Step 4
				some getToken
				MyApp + Google in e3.procs
		}
*/

} for 6//5 but 7 Event

/*
fun to : Proc -> Proc -> Step {
	{p1, p2 : Proc, s : Step |
		p1 in s.e.sender and
		p2 in s.e.receiver and
		(p1 + p2 in OAuthModules or p1 + p2 in (Server + Browser)) }
}	

fun learns : Proc -> Data -> Step {
	{ p : Proc, d : Data, s : Step |
		let evt = s.e {
			(p in evt.sender and d in evt.rets) or
			(p in evt.receiver and d in evt.args)
		} 
	}
}
*/
