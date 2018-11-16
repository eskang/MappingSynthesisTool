/**
	* OAuth.als
	* 
	* A model of OAuth
	* Based on the OAuth spec: http://tools.ietf.org/html/rfc6749
	* Protocol mode: Authorization code grant
	*/
module OAuth

open HTTP
//open HTTPWithSteps

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
abstract sig ReqToken extends Data {}
abstract sig UserCred extends Data {}		
abstract sig AccessToken extends Data {}	// access token

one sig idAlice, idEve extends OAuthID {}
one sig requestTokenA, requestTokenB extends ReqToken {}
one sig credAlice, credEve extends UserCred {}
one sig accessTokenAlice, accessTokenEve extends AccessToken {}

/**
* Abstract labels
*/

-- auxiliary stuff
fun OAuthModules : set Module {
	AuthServer + Client + UserAgent
}
fun OAuthData : set Data {
	ReqToken + AccessToken  + UserCred + OAuthID + Session
}
fun OAuthLabel : set Event {
	authorize + authorized + retrieveReqToken + getRequestToken + 
	getAccessToken + initiate + OtherOp //+ ReadResource + GetResource 
}

/**
	* Participanting components
	*/
// Authorization server, which grants OAuthClient access to a resource. 
abstract sig AuthServer extends Module {
	creds : OAuthID -> lone UserCred
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

// 0. initiate
// from UserAgent to Client
sig initiate extends DataflowLabel {
	session : Session
}{
	no args & OAuthData
	rets & OAuthData = session
	some sender & UserAgent 
	some receiver & MyApp
}

// 1. getRequestToken
// from Client to AuthServer
sig getRequestToken extends DataflowLabel {
	reqToken : ReqToken		
}{
	no args & OAuthData
	rets & OAuthData = reqToken
	some sender & Client 
	some receiver & AuthServer
}

// 2. Retrieve request token from the client
// from UserAgent to Client
sig retrieveReqToken extends DataflowLabel {
	session : Session,
	reqToken : ReqToken			
}{
	args & OAuthData = session
	rets & OAuthData = reqToken
	some sender & UserAgent 
	some receiver & MyApp	
}

// 3. Authentication step
// from UserAgent to AuthServer
// AuthServer authenticates the user and
// returns a corresponding authorization code
sig authorize extends DataflowLabel {
	userid : OAuthID,
	cred : UserCred,
	reqToken : ReqToken
}{
	args & OAuthData = cred + userid + reqToken
	no rets & OAuthData
	some UserAgent & sender 
	some AuthServer & receiver
}

// 4. Pass auth code
// from UserAgent to OAuthClient
// User passes the authorization code to the client
sig authorized extends DataflowLabel {
	session : Session
}{
	args & OAuthData = session
	no rets & OAuthData
	some sender & UserAgent 
	some receiver & Client
}

// 5. Requesting access token
// from OAuthClient to AuthServer
// The client sends the authorization code directly to the auth server
// to receive an access token
sig getAccessToken extends DataflowLabel {
	reqToken : ReqToken,
	accessToken : AccessToken
}{
	args & OAuthData = reqToken
	rets & OAuthData = accessToken
	some sender & Client 
	some receiver & AuthServer
}

sig OtherOp extends DataflowLabel {}{	
	some sender & AliceBrowser
	some receiver & EvilServer
	this not in RedirectReq 
		implies no args & (UserCred + ReqToken + Session + NONCE)
}

-------------

/** 
	* Instantiation 
	*/
one sig Alice extends UserAgent {}{
	id = idAlice
	cred = credAlice
	owns = cred + idAlice
	
	// user behavior	
}

one sig Eve extends UserAgent {}{
	id = idEve
	cred = credEve
	owns = cred + idEve
}
one sig MyApp extends Client {}{
	owns = Session
}

pred myApp_sessions[e : Event, i : Session, u : UserAgent] {
	some e' : e.prevs & initiate |
		u in e'.sender and i = e'.session
}

pred myApp_reqTokens[e : Event, i : Session, r : ReqToken] {
	some e' : e.prevs & getRequestToken |
			i = e'.prev.(initiate <: session) and r = e'.reqToken
}

pred myApp_accessTokens[e : Event, i : Session, t : AccessToken] {
	some e' : e.prevs & getAccessToken |
		t = e'.accessToken and
		myApp_reqTokens[e', i, e'.reqToken] 
}

// App related datatypes and 
abstract sig Session extends Data {}
one sig sessionX extends Session {}
one sig sessionY extends Session {}

one sig Google extends AuthServer {}{
	creds = idAlice -> credAlice + idEve -> credEve
	owns = ReqToken + AccessToken + UserCred
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
	owns in MyApp.@owns
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
	UserAgent -> (authorize + authorized + retrieveReqToken + initiate) + // + ReadResource) + 
	Client -> (authorized + getRequestToken + retrieveReqToken +
			getAccessToken + initiate) + // + GetResource +  + ReadResource) + 
	AuthServer -> (authorize + getRequestToken + getAccessToken) + // + GetResource)
	OAuthModules -> OtherOp +
	// from HTTP
	Browser -> HTTPReq + 
	Server -> HTTPReq 
}

one sig path_authorize,path_initiate,path_authorized,
path_retrieve, path_getRequestToken, 
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

/**
	* Behaviors
	*/

pred assumptions {
}

pred userConstraint {
	// Every mapping should allow some behavior that is defined in "scenario"
	// This is to ensure that the mapping is not too restrictive
	all o : OAuthLabel | o in HTTPReq
}


pred google_req2access[e : Event, r: ReqToken, a : AccessToken] {
	some e' : e.prevs & authorize {
		(e'.userid = idAlice and r = e'.reqToken and a = accessTokenAlice) or
		(e'.userid = idEve and r = e'.reqToken and a = accessTokenEve)
	}
}

pred processBehavior_OAuth {
	// User agent behavior
	all o : authorize, u : o.sender & UserAgent & Trusted {
		o.userid = u.id and o.cred = u.cred
	}

	// AuthServer behavior
	all o : authorize {
		o.userid -> o.cred in Google.creds 
		all o' : o.prevs & authorize |
			o.reqToken != o'.reqToken
	}

	all o : getRequestToken {
		all o' : o.prevs & getRequestToken {
			o.reqToken != o'.reqToken
		}
	}

	all o : getAccessToken {
		// AccessTokenReq must provide an authorization grant that corresponds to
		// the access token returned
		google_req2access[o, o.reqToken, o.accessToken]
	}
	
	// MyApp behavior
	all o : initiate {
		all o' : o.prevs & initiate {
			o.session != o'.session
		}
	}
		
	all o : retrieveReqToken {
		myApp_reqTokens[o, o.session, o.reqToken]
	}
		
	all a : getRequestToken {
		a.prev in initiate
	}

	all o : authorized | let o' = o.next {
		o' in getAccessToken
	}

	all o : getAccessToken | let o' = o.prev {
		o' in authorized
		myApp_reqTokens[o, o'.(authorized <: session), o.reqToken]
	}
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
			all c : r.cookie {
				// Every cookie included in this request matches the origin of the request URL
				c.origin = r.url_origin 
				// There must have been a set-cookie header received as part of a previous request
				some r' : r.prevs & procs.b & HTTPReq |
					c in r'.resp_set_cookie & SetCookie and c.origin = c.set_origin
			}
		}
	}

	all b : Browser, r : RedirectReq {
		b in r.sender implies
			some r' : r.prev & procs.b & HTTPReq  |
				r' = r.trigger and
				no r.body and
				r.url_origin in r'.resp_redirectTo_origin and
				r.url_path in r'.resp_redirectTo_path and
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
		myApp_tokens[procs, labels, e, id, accessTokenAlice] implies	
			Eve -> e -> id not in knows[procs, labels]	
*/
	all e : Event, id : Session |
		myApp_accessTokens[e, id, accessTokenEve] implies	
			not myApp_sessions[e, id, Alice]
}

pred oauthProperty2 {
	all e : Event, id : Session |
		myApp_accessTokens[e, id, accessTokenAlice] implies	
			not myApp_sessions[e, id, Eve]
}

pred processBehavior {
	// General dataflow behavior
	all e : Event, p : Proc |	
		(p in e.sender implies e.args in p.knows.e) and
		(p in e.receiver implies e.rets in e.args + p.knows.e)

	processBehavior_OAuth
	processBehavior_HTTP
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

pred scenario1 {
	some e : Event, id : Session |  
		myApp_accessTokens[e, id, accessTokenAlice] 
		and Alice -> id -> e in knows
}
pred scenario2 {
	some e : Event, id : Session |  
		myApp_accessTokens[e, id, accessTokenEve] 
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
}

pred mappingLiveness2 {
	userConstraint
	mappingConstraints
	behavior
	scenario2
}

pred mappingSafety {
	userConstraint
	mappingConstraints
	behavior
	not oauthProperty2
}


abstract sig NONCE extends Data {}

run {
	userConstraint
	behavior	
//	scenario1
//	scenario2
	not oauthProperty2
} for 3 but 8 Event//, 8 Step
/*
run checkTest {
	userConstraint
	testMapping2
	behavior
	//not oauthProperty2
	//scenario1
	scenario2
} for 3 but 7 Event, 7 Step

one sig NONCE2, NONCE3 extends NONCE {}

pred mappingConstraints {}

pred testMapping1 {
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
  // mapping from authorized to port_client
  all a : authorized | let b = a { b in port_client
    no b.resp_resource.content
    b.cookie = a.session
    no b.url_query
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_authorized
    no b.url_query2
  }
  // mapping from retrieveReqToken to port_client
  all a : retrieveReqToken | let b = a { b in port_client
    b.resp_resource.content = a.reqToken
    b.cookie = a.session
    no b.url_query
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_retrieve
    no b.url_query2
  }
  // mapping from authorize to port_auth_server
  all a : authorize | let b = a { b in port_auth_server
    no b.resp_resource.content
    no b.cookie
    b.url_query = a.userid
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    b.body = a.cred
    no b.resp_redirectTo_query2
    b.url_path = path_authorize
    b.url_query2 = a.reqToken
  }
  // mapping from getRequestToken to port_auth_server
  all a : getRequestToken | let b = a { b in port_auth_server
    b.resp_resource.content = a.reqToken
    no b.cookie
    no b.url_query
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_getRequestToken
    no b.url_query2
  }
  // mapping from getAccessToken to port_auth_server
  all a : getAccessToken | let b = a { b in port_auth_server
    b.resp_resource.content = a.accessToken
    no b.cookie
    b.url_query = a.reqToken
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_getAccessToken
    some b.url_query2
  }
}

pred testMapping2 {
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
  // mapping from authorized to port_client
  all a : authorized | let b = a { b in port_client
    no b.resp_resource.content
    b.cookie = a.session
	//
    some b.url_query
	//
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_authorized
    no b.url_query2
  }
  // mapping from retrieveReqToken to port_client
  all a : retrieveReqToken | let b = a { b in port_client
    b.resp_resource.content = a.reqToken
    b.cookie = a.session
    no b.url_query
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_MYAPP
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_retrieve
    no b.url_query2
  }
  // mapping from authorize to port_auth_server
  all a : authorize | let b = a { b in port_auth_server
	//	
    (b.url_query2 = requestTokenA) implies b.resp_resource.content = NONCE2
    (b.url_query2 = requestTokenB) implies b.resp_resource.content = NONCE2
	//
    no b.cookie
    b.url_query = a.userid
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    b.body = a.cred
    no b.resp_redirectTo_query2
    b.url_path = path_authorize
    b.url_query2 = a.reqToken
  }
  // mapping from getRequestToken to port_auth_server
  all a : getRequestToken | let b = a { b in port_auth_server
    b.resp_resource.content = a.reqToken
    no b.cookie
    no b.url_query
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_getRequestToken
    no b.url_query2
  }
  // mapping from getAccessToken to port_auth_server
  all a : getAccessToken | let b = a { b in port_auth_server
    b.resp_resource.content = a.accessToken
    no b.cookie
    b.url_query = a.reqToken
	//
    (b.url_query = requestTokenA) implies b.url_query2 = NONCE2    
    (b.url_query = requestTokenB) implies b.url_query2 = NONCE3
	//
    no b.resp_set_cookie
    b.resp_code = OK
    no b.resp_redirectTo_query
    b.url_origin = ORIGIN_GOOGLE
    no b.resp_redirectTo_origin
    no b.resp_redirectTo_path
    no b.body
    no b.resp_redirectTo_query2
    b.url_path = path_getAccessToken
  }
}
*/

run {
	userConstraint
	behavior
	all r : retrieveReqToken | no r.resp_redirectTo_origin
/*
	some initiate
	some getRequestToken
	some retrieveReqToken
	some authorize
	some getAccessToken
*/
//	scenario1
//	scenario2
//	not oauthProperty
	not oauthProperty2
/*	
	some e : Event {
		 e = first 
		let e0 = e.next, e1 = e0.next, e2 = e1.next, e3 = e2.next, 
			e4 = e3.next, e5 = e4.next,
			aliceInit = e & initiate, 
			eveInit = e0 & initiate, 
			getReqToken = e1 & getRequestToken, 
			eveReqToken = e2 & retrieveReqToken,
			aliceVisit = e3 & OtherOp, 
			aliceAuth = e4 & authorize, 
			getToken = e5 & getAccessToken {
				// Step 0
				some aliceInit
				Alice + MyApp in aliceInit.procs
				// Step 1
				some eveInit
				Eve + MyApp in eveInit.procs 
				// Step 2
				some getReqToken
				MyApp + Google in getReqToken.procs		
				// Step 2.5
				some eveReqToken
				Eve + MyApp in eveReqToken.procs
				// Step 3
				some aliceVisit
				AliceBrowser + EvilServer in aliceVisit.procs
				// Step 4
				some aliceAuth
				Alice + Google in aliceAuth.procs
				// Step 5
				some getToken
				MyApp + Google in getToken.procs
		}
	}
*/
} for 4 but 7 Event//, 7 Step

run { 
	userConstraint
	behavior
	some e : Event, id : Session |  
		myApp_accessTokens[e, id, accessTokenAlice] 
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
				codeEve in eveAuth.rets			
				// Step 3
				some aliceVisit
				e2.procs = AliceBrowser + EvilServer
				codeEve in aliceVisit.rets
				// Step 4
				some aliceForward				
				Alice + MyApp in e3.procs
				codeEve = aliceForward.code
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
				codeAlice in aliceAuth.rets 
				some (aliceAuth.m).redirectTo
				//(aliceInit.m).responseHeaders & Hash in (aliceAuth.m).redirectTo.query
				// Step 3
				some aliceForward
				Alice + MyApp in e2.procs
				codeAlice = aliceForward.code
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
				codeEve in eveAuth.rets			
				// Step 3
				some aliceVisit
				Alice + AliceBrowser + Eve + EvilServer = e2.procs
				aliceVisit.resp_redirectTo_origin = ORIGIN_MYAPP
				aliceVisit.resp_redirectTo_path = path_forward
				codeEve in aliceVisit.rets

				// Step 4
				some aliceForward		
				Alice + MyApp in e3.procs
				Alice -> codeEve -> e3 in knows
				codeEve = aliceForward.code
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
				codeAlice in aliceAuth.rets 
				some (aliceAuth.m).redirectTo
//				(aliceInit.m).responseHeaders & Hash in (aliceAuth.m).redirectTo.query
				// Step 3
				some aliceForward
				Alice + MyApp in e2.procs
				codeAlice = aliceForward.code
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

