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
	ReqToken + AccessToken  + UserCred + OAuthID + Session + NONCE
}
fun OAuthLabel : set Event {
	Authorize + Authorized + RetrieveReqToken + GetRequestToken + 
	GetAccessToken + Initiate + OtherOp //+ ReadResource + GetResource 
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

// 0. Initiate
// from UserAgent to Client
sig Initiate extends DataflowLabel {
	session : Session
}{
	no args & OAuthData
	rets & OAuthData = session
	some sender & UserAgent 
	some receiver & MyApp
}

// 1. GetRequestToken
// from Client to AuthServer
sig GetRequestToken extends DataflowLabel {
	reqToken : ReqToken		
}{
	no args & OAuthData
	rets & OAuthData = reqToken
	some sender & Client 
	some receiver & AuthServer
}

// 2. Retrieve request token from the client
// from UserAgent to Client
sig RetrieveReqToken extends DataflowLabel {
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
sig Authorize extends DataflowLabel {
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
sig Authorized extends DataflowLabel {
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
sig GetAccessToken extends DataflowLabel {
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
	some e' : e.prevs & Initiate |
		u in e'.sender and i = e'.session
}

pred myApp_reqTokens[e : Event, i : Session, r : ReqToken] {
	some e' : e.prevs & GetRequestToken |
			i = e'.prev.(Initiate <: session) and r = e'.reqToken
}

pred myApp_accessTokens[e : Event, i : Session, t : AccessToken] {
	some e' : e.prevs & GetAccessToken |
		t = e'.accessToken and
		myApp_reqTokens[e', i, e'.reqToken] 
}

// App related datatypes and 
abstract sig Session extends Data {}
one sig session_X extends Session {}
one sig session_Y extends Session {}

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
	owns in Google.@owns
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
	UserAgent -> (Authorize + Authorized + RetrieveReqToken + Initiate) + // + ReadResource) + 
	Client -> (Authorized + GetRequestToken + RetrieveReqToken +
			GetAccessToken + Initiate) + // + GetResource +  + ReadResource) + 
	AuthServer -> (Authorize + GetRequestToken + GetAccessToken) + // + GetResource)
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
	some e' : e.prevs & Authorize {
		(e'.userid = idAlice and r = e'.reqToken and a = accessTokenAlice) or
		(e'.userid = idEve and r = e'.reqToken and a = accessTokenEve)
	}
}

pred processBehavior_OAuth {
	// User agent behavior
	all o : Authorize, u : o.sender & UserAgent & Trusted {
		o.userid = u.id and o.cred = u.cred
	}

	// AuthServer behavior
	all o : Authorize {
		o.userid -> o.cred in Google.creds
	}

	all o : GetRequestToken {
		all o' : o.prevs & GetRequestToken {
			o.reqToken != o'.reqToken
		}
	}

	all o : GetAccessToken {
		// AccessTokenReq must provide an authorization grant that corresponds to
		// the access token returned
		google_req2access[o, o.reqToken, o.accessToken]
	}
	
	// MyApp behavior
	all o : Initiate {
		all o' : o.prevs & Initiate {
			o.session != o'.session
		}
	}
		
	all o : RetrieveReqToken {
		myApp_reqTokens[o, o.session, o.reqToken]
	}
		
	all a : GetRequestToken {
		a.prev in Initiate
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

/*
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
	not oauthProperty
}
*/

abstract sig NONCE extends Data {}

/*
run checkTest {
	userConstraint
	testMapping1
	behavior
	//not oauthProperty
	scenario1
	scenario2
} for 3 but 9 Event

one sig NONCE2, NONCE3 extends NONCE {}

pred testMapping1 {
// mapping from GetAccessToken to port_auth_server
  all a : GetAccessToken | let b = a { b in port_auth_server
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
  // mapping from Forward to port_client
  all a : Forward | let b = a { b in port_client
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
  all a : Authorize | let b = a { b in port_auth_server
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
  // mapping from Initiate to port_client
  all a : Initiate | let b = a { b in port_client
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
// mapping from GetAccessToken to port_auth_server
  all a : GetAccessToken | let b = a { b in port_auth_server
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
  // mapping from Forward to port_client
  all a : Forward | let b = a { b in port_client
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
  all a : Authorize | let b = a { b in port_auth_server
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
    b.url_path = path_authorize
  }
  // mapping from Initiate to port_client
  all a : Initiate | let b = a { b in port_client
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
	all r : RetrieveReqToken | no r.resp_redirectTo_origin
/*
	some Initiate
	some GetRequestToken
	some RetrieveReqToken
	some Authorize
	some GetAccessToken
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
			aliceInit = e & Initiate, 
			eveInit = e0 & Initiate, 
			getReqToken = e1 & GetRequestToken, 
			eveReqToken = e2 & RetrieveReqToken,
			aliceVisit = e3 & OtherOp, 
			aliceAuth = e4 & Authorize, 
			getToken = e5 & GetAccessToken {
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
} for 4 but 7 Event, 7 Step

run { 
	userConstraint
	behavior
	some e : Event, id : Session |  
		myApp_accessTokens[e, id, accessTokenAlice] 
		and Alice -> id -> e in knows
/*
	let e0 = first, e1 = first.next, e2 = e1.next {//, e3 = e2.next, e4 = e3.next {
		e0 in Initiate & HTTPReq
		Alice in e0.sender	
		MyApp in e0.receiver
		e1 in Authorize
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
			aliceInit = e.labels & Initiate, 
			eveInit = e0.labels & Initiate, eveAuth = e1.labels & Authorize, aliceVisit = e2.labels & HTTPReq, 
			aliceForward = e3.labels & ForwardToMyApp, getToken = e4.labels & GetAccessToken {
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
			aliceInit = e0.labels & Initiate, aliceAuth = e1.labels & Authorize,  
			aliceForward = e2.labels & ForwardToMyApp, getToken = e3.labels & GetAccessToken {
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
			aliceInit = e &  Initiate, 
			eveInit = e0 & Initiate, eveAuth = e1 & Authorize, aliceVisit = e2 & HTTPReq, 
			aliceForward = e3 & ForwardToMyApp, getToken = e4 & GetAccessToken {
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
			aliceInit = e0.labels & Initiate, aliceAuth = e1.labels & Authorize,  
			aliceForward = e2.labels & ForwardToMyApp, getToken = e3.labels & GetAccessToken {
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

