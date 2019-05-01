/**
	* OAuth.als
	* 
	* A model of OAuth
	* Based on the OAuth spec: http://tools.ietf.org/html/rfc6749
	* Protocol mode: Authorization code grant
	*/
module OAuth

open HTTP

fun senders[procs : Event -> Proc, labels : Event -> Label] : Event -> Label -> Proc {
	{ e : Event, l : Label, p : Proc |
		l in e.labels and p in e.procs & l.sender and {
			(l in Authorize and p in UserAgent) or
			(l in Forward and p in UserAgent) or
			(l in GetAccessToken and p in Client) or
//			(l in GetResource and p in Client) or
			(l in Initiate and p in UserAgent) or
//			(l in ReadResource and p in UserAgent)
			// from HTTP
			(l in HTTPReq and p in Browser + Server)
		}
	}
}

fun receivers[procs : Event -> Proc, labels : Event -> Label] : Event -> Label -> Proc {
	{ e : Event, l : Label, p : Proc | 
		l in e.labels and p in e.procs & l.receiver and {
			(l in Authorize and p in AuthServer) or
			(l in Forward and p in Client) or
			(l in GetAccessToken and p in AuthServer) or
//			(l in GetResource and p in AuthServer) or
			(l in Initiate and p in Client) or
//			(l in ReadResource and p in Client)
			// from HTTP
			(l in HTTPReq and p in Server)
		}			
	}
}


// A process that performs an event is either one of its senders or receivers
fun performer[procs : Event -> Proc, labels : Event -> Label] : Event -> Label -> Proc {
	senders[procs, labels] + receivers[procs, labels]
}

fun composedWith : Proc -> Proc {
	MyApp -> ClientServer +
	Google -> AuthHTTPServer +
	Alice -> AliceBrowser +
	Eve -> EvilServer
}

fun knows[procs : Event -> Proc, labels : Event -> Label] : Proc -> Event -> Data {
	{ p : Proc, e : Event, d : Data |
		d in p.owns or
		some e' : e.prevs, l : Label |
			(d in l.args and p in receivers[procs, labels][e'][l] //and some senders[procs,labels][e'][l]
			) or
			(d in l.rets and p in senders[procs, labels][e'][l] //and some receivers[procs,labels][e'][l]
			)
	}
}


/**
	*  OAuth-related datatypes
	*/
abstract sig OAuthID {}
abstract sig Token extends Data {}
abstract sig Resource extends Data {}
abstract sig AuthCode extends Token {}		// authorization grant
abstract sig UserCred extends Token {}		
abstract sig AccessToken extends Token {}	// access token

one sig AliceID, EveID extends OAuthID {}
one sig AliceRes, EveRes extends Resource {}
one sig AliceCode, EveCode extends AuthCode {}
one sig AliceCred, EveCred extends UserCred {}
one sig AliceToken, EveToken extends AccessToken {}

/**
* Abstract labels
*/

-- auxiliary stuff
fun OAuthModules : set Module {
	AuthServer + Client + UserAgent
}
fun OAuthData : set Data {
	Token + Resource
}
fun OAuthLabel : set Label {
	Authorize + Forward + GetAccessToken + Initiate //+ ReadResource + GetResource 
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
abstract sig Authorize extends DataflowLabel {
	userID : OAuthID,
	userCred : UserCred,
	code : AuthCode	
}{
	args = userCred
	rets = code
	sender in UserAgent and receiver in AuthServer
}

// 2. Pass auth code
// from UserAgent to OAuthClient
// User passes the authorization code to the client
abstract sig Forward extends DataflowLabel {
	code : AuthCode
}

// 3. Requesting access token
// from OAuthClient to AuthServer
// The client sends the authorization code directly to the auth server
// to receive an access token
abstract sig GetAccessToken extends DataflowLabel {
	code : AuthCode,
	token : AccessToken
}{
	args = code
	rets = token
	sender in Client and receiver in AuthServer
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
	id = AliceID
	cred = AliceCred
	owns = cred
}
one sig Eve extends UserAgent {}{
	id = EveID
	cred = EveCred
	owns = cred
}
one sig MyApp extends Client {}{
	owns = AppID + Hash
}

pred myApp_codes[procs : Event -> Proc, labels : Event -> Label, e : Event, i : AppID, c : AuthCode] {
	some e' : e.prevs & procs.MyApp, l : e'.labels & ForwardToMyApp |
			i = l.id and c = l.code	
}

pred myApp_tokens[procs : Event -> Proc, labels : Event -> Label, e : Event, i : AppID, t : AccessToken] {
	some e' : e.prevs & procs.MyApp, l : e'.labels & GetAccessToken |
		t = l.token and
		myApp_codes[procs,labels,e', i, l.code] 
}

/*
fun myApp_resources[procs : Event -> Proc, labels : Event -> Label] : Event -> AppID -> Resource {
	{ e : Event, i : AppID, r : Resource |
		some e' : e.prevs & procs.MyApp, l : e'.labels & GetResource |
			r = l.res and
			e' -> i -> l.token in myApp_tokens[procs, labels]
	}
}
*/

// App related datatypes and 
abstract sig AppData extends Data {}
abstract sig AppID extends Data {}
one sig AppID_X extends AppID {}
one sig AppID_Y extends AppID {}

abstract sig Hash extends Data {}
one sig HashX, HashY extends Hash {}

abstract sig Initiate extends DataflowLabel {
	appID : AppID
}{
	no args
	rets = appID
	sender in UserAgent and receiver in MyApp
}
abstract sig ForwardToMyApp extends Forward {
	id : AppID
}{
	args = id + code
	no rets
	sender in UserAgent and receiver in MyApp
}
/*
abstract sig ReadResource extends DataflowLabel {
	appID : AppID,
	res : Resource
}{
	args = appID 
	rets = res
}
*/

one sig Google extends AuthServer {}{
	tokens = AliceCode -> AliceToken + EveCode -> EveToken
	codes = AliceCred -> AliceCode + EveCred -> EveCode
	creds = AliceID -> AliceCred + EveID -> EveCred
	owner = AliceRes -> AliceID + EveRes -> EveID
	resACL = AliceRes -> AliceToken + EveRes -> EveToken
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
	no owns
}
one sig ClientServer extends Server {}{
	host = HostMyApp
	no owns
}
one sig EvilServer extends Server {}{
	host = HostEvil
	no owns
}
one sig AliceBrowser extends Browser {}{
	no addr
	no owns
}
//one sig EveBrowser extends Browser {}{ no addr }

fun alpha : Proc -> Label {
	UserAgent -> (Authorize + Forward + Initiate) + // + ReadResource) + 
	Client -> (Forward + GetAccessToken + Initiate) + // + GetResource +  + ReadResource) + 
	AuthServer -> (Authorize + GetAccessToken) + // + GetResource)
	// from HTTP
	Browser -> HTTPReq + 
	Server -> HTTPReq
}

one sig URLMyApp extends URL {}{ origin = OriginMyApp }
one sig URLGoogle extends URL {}{ origin = OriginGoogle }
one sig URLEvilServer extends URL {}{ origin = OriginEvil }
one sig OriginMyApp extends Origin {}{ host = HostMyApp }
one sig OriginGoogle extends Origin {}{ host = HostGoogle }
one sig OriginEvil extends Origin {}{ host = HostEvil }
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

pred userConstraint[mapping : Label -> Label]{
	// Every mapping should allow some behavior that is defined in "scenario"
	// This is to ensure that the mapping is not too restrictive
/*
	(some procs : Event -> Proc, labels : Event -> Label | 
		applyMapping[mapping, procs, labels] and behavior[procs, labels] and scenario1[procs, labels]) 
	(some procs : Event -> Proc, labels : Event -> Label | 
		applyMapping[mapping, procs, labels] and behavior[procs, labels] and scenario2[procs, labels]) 
	(some procs : Event -> Proc, labels : Event -> Label | 
		applyMapping[mapping, procs, labels] and behavior[procs, labels] and scenario3[procs, labels]) 
*/

	// Can't map a label to itself
	no iden & mapping
	// Can't map an abstract (concrete) label to another abstract (concrete) label
	no m1, m2 : OAuthLabel | m1 -> m2 in mapping
	no m1, m2 : HTTPReq | m1 -> m2 in mapping

	all o : OAuthLabel | one o.mapping and o.mapping in HTTPReq
	all o : OAuthLabel, r : o.mapping |
		(r.url_query + r.headers + r.body) & (OAuthData + AppID) in o.args and
		(r.responseHeaders + r.resource.tags + r.redirectTo_query) & (OAuthData + AppID) in o.rets

	all i : Initiate, r : i.mapping {
		r.responseHeaders = i.appID
		i.appID in SetCookie
		no r.resource.tags 
		r.redirectTo.origin = OriginGoogle
	}

	all a : Authorize, r : a.mapping {		
		r.redirectTo_query & AuthCode = a.code
		r.redirectTo.origin = OriginMyApp
		r.receiver in AuthHTTPServer
	}

	all f : Forward, r : f.mapping {
		f.id in r.headers & Cookie	
		no r.redirectTo
	}
	
	all f : Forward, r : f.mapping {
		some r.url_query & Hash implies
			some i : Initiate, r' : i.mapping |
				r.url_query & Hash in r'.redirectTo_query				
	}

	all a : Authorize, r : a.mapping {
		some r.url_query & Hash implies
			some i : Initiate, r' : i.mapping |
				r.url_query & Hash in r'.redirectTo_query				
	}

/*
	all r : HTTPReq | 
		r.receiver in ClientServer implies some r.mapping & (Forward + Initiate)
	all r : HTTPReq | 
		r.receiver in AuthHTTPServer implies some r.mapping & (GetAccessToken + Authorize)
	all r : HTTPReq |
		AliceCred in r.args implies some r.mapping & Authorize
	all r : HTTPReq |
		AliceCode in r.args implies some r.mapping & (Forward + GetAccessToken)
	all r : HTTPReq |
		some AppID & r.args implies some r.mapping & (Forward + Authorize)
	all r : HTTPReq |
		some Hash & r.args implies some r.mapping & (Forward + Authorize)
	all r : HTTPReq |
		some AliceCode & r.rets implies some r.mapping & Authorize
	all r : HTTPReq |
		some AliceToken & r.rets implies some r.mapping & GetAccessToken	
*/
}

pred labelConstraint[labels : set Label, procs : set Proc] {
	no disj l1, l2 : labels | 
		(l1 + l2 in OAuthLabel) or 
		(l1 + l2 in HTTPReq)
	some Authorize & labels implies  some AuthServer & procs
	some Forward & labels implies some Client & procs
	some GetAccessToken & labels implies some AuthServer & procs 
//	some GetResource & labels implies some AuthServer & procs
	some Initiate & labels implies some Client & procs
//	some ReadResource & labels implies some Client & procs
	// from HTTP
	some HTTPReq & labels implies some Server & procs
}

pred processBehavior_OAuth[procs : Event -> Proc, labels : Event -> Label] {
	// User agent behavior
	all e : Event, o : Authorize & e.labels, u : e.procs & UserAgent & Trusted {
		o.userID = u.id and o.userCred = u.cred
	}

	// AuthServer behavior
	all e : Event, o : Authorize & e.labels, s : e.procs & AuthServer & Trusted {
		o.userID -> o.userCred in s.creds
		// AuthReq must provide a OAuth user credential that corresponds to
		// the authorization grant returned 	
		o.userCred -> o.code in s.codes
	}

	all e : Event, o : GetAccessToken & e.labels, s : e.procs & AuthServer & Trusted {
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
	all e : procs.MyApp, o : Initiate & e.labels {
		all e' : e.prevs & procs.MyApp, o' : Initiate & e'.labels {
			o.appID != o'.appID
		}
	}
		
	all e : procs.MyApp, f : ForwardToMyApp & e.labels {
		some e' : e.prevs & procs.MyApp, o : Initiate & e'.labels {
			o.appID = f.id
		}
	}

/*
	all e : procs.MyApp, o : ReadResource {
		e -> o in labels implies
			e -> o.appID -> o.res in myApp_resources[procs, labels]
	}
*/

}

pred processBehavior_HTTP[procs : Event -> Proc, labels : Event -> Label] {
	/**
	HTTP servers
	*/
	// only accepts requests with the same host as the server
	all e : Event, s : Server, r : HTTPReq {
		(e -> r in labels and e -> s in procs and s in receivers[procs,labels][e][r]) implies {
			r.url.origin.host = s.host
			// return the cookie with the right origin
			all c : Cookie | c in r.rets implies c.origin = r.url.origin
		}
	}

	/**
	Browser
	*/
	all e : Event, b : Browser, r : HTTPReq {
		(e -> r in labels and e -> b in procs and b in senders[procs,labels][e][r]) implies {
			all c : Cookie | 
				// Every cookie included in this request matches the origin of the request URL
				c in r.headers implies {
					c.origin = r.url.origin
					// There must have been a set-cookie header received as part of a previous request
					some e' : e.prevs & procs.b, r' : e'.labels & HTTPReq |
						c in r'.responseHeaders & SetCookie and c.origin = c.set_origin
				}
		}
	}

	all e : Event, b : Browser, r : RedirectReq {
		(e -> r in labels and e -> b in procs and b in senders[procs,labels][e][r]) implies
			some e' : e.prevs & procs.b, r' : e'.labels & HTTPReq |
				r' = r.trigger and
				r.url in r'.redirectTo and
				r.url_query in r'.redirectTo_query
	}

}

/**
	Property 
*/

pred applyMapping[mapping : Label -> Label, procs : Event -> Proc, labels : Event -> Label] {
	all l1, l2 : Label |
		l1 -> l2 in mapping implies {
			all e : Event | 
				e -> l1 in labels implies {
					// then every event that contains l1 must also contain l2
					e -> l2 in labels and
					composedWith[performer[procs, labels][e][l1]] in e.procs
				}
		}
	all e : Event, r : HTTPReq |
		(e -> r in labels and some (AuthHTTPServer + ClientServer) & performer[procs,labels][e][r]) implies
			(some mapping.r & e.labels)
	all e : Event, r : UserReq |
		(e -> r in labels and  AliceBrowser in senders[procs,labels][e][r]) implies
			(some mapping.r & e.labels)
}

pred oauthProperty[procs : Event -> Proc, labels : Event -> Label] {
/*
	all e : Event, r : ReadResource |
		e -> r in labels and r.res = AliceRes implies
			Eve not in e.procs
*/
/*
	all e : Event, id : AppID |
		myApp_tokens[procs, labels, e, id, AliceToken] implies	
			Eve -> e -> id not in knows[procs, labels]	
*/
	all e : Event, id : AppID |
		myApp_tokens[procs, labels, e, id, EveToken] implies	
			Alice -> e -> id not in knows[procs, labels]	
}

pred processBehavior[procs : Event -> Proc, labels : Event -> Label] {
	// General dataflow behavior
	all e : Event, l : Label, p : Proc |	
		(e-> l -> p in senders[procs, labels] implies
			l.args in knows[procs, labels][p + composedWith.p + composedWith[p]][e]) and
		(e -> l -> p in receivers[procs, labels] implies
			l.rets in l.args + knows[procs, labels][p + composedWith.p + composedWith[p]][e])

	processBehavior_OAuth[procs, labels]
	processBehavior_HTTP[procs, labels]

/*
	all e : Event, s : Server, r : HTTPReq {
		// servers don't expose Alice's credential
		(e -> r in labels and e -> s in procs and s in receivers[procs,labels][e][r]) implies {
			AliceCred not in r.rets
		}
	}
*/
}

pred behavior[procs : Event -> Proc, labels : Event -> Label] {
	all e : Event {
		some e.labels
		all l : e.labels | some senders[procs,labels][e][l] and some receivers[procs,labels][e][l]
		labelConstraint[e.labels, e.procs] 
		all p : e.procs | some e.labels & alpha[p] and p in e.labels.(sender + receiver)
	}
	processBehavior[procs, labels]
}

pred goodMapping[m : Label -> Label] {
	all procs : Event -> Proc, labels : Event -> Label |
		(applyMapping[m, procs, labels] and behavior[procs, labels]) implies
			oauthProperty[procs, labels]
}

pred scenario1[procs : Event -> Proc, labels : Event -> Label] {
	some e : Event, id : AppID |  
		myApp_tokens[procs, labels, e, id, AliceToken] 
		and Alice -> e -> id in knows[procs, labels]
}
pred scenario2[procs : Event -> Proc, labels : Event -> Label] {
	some e : Event, id : AppID |  
		myApp_tokens[procs, labels, e, id, EveToken] 
		and Eve -> e -> id in knows[procs, labels]
}
pred scenario3[procs : Event -> Proc, labels : Event -> Label] {
	some e : Event, r : e.labels & HTTPReq | 
		EvilServer in receivers[procs,labels][e][r]
}

run {
	some m : OAuthLabel -> HTTPReq | 
		userConstraint[m] and goodMapping[m] 
} for 1 but 7 Event


run  {
	some m : OAuthLabel -> HTTPReq | 
		userConstraint[m] and goodMapping[m] and
		no m' : OAuthLabel -> HTTPReq {
			userConstraint[m] and goodMapping[m] and 
			some procs : Event -> Proc, labels : Event -> Label {
				(applyMapping[m, procs, labels] and not behavior[procs, labels]) and
				(applyMapping[m', procs, labels] and behavior[procs, labels])
			}
		}
} for 1 but 7 Event


run { 
	some m : Label -> Label | 
	userConstraint[m] and 
	some procs : Event -> Proc, labels : Event -> Label {
		applyMapping[m, procs, labels]
		behavior[procs, labels]

		some e : Event, id : AppID |  
			myApp_tokens[procs, labels, e, id, AliceToken] 
			and Alice -> e -> id in knows[procs, labels]


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
				EveCode in eveAuth.rets			
				// Step 3
				some aliceVisit
				e2.procs = AliceBrowser + EvilServer
				EveCode in aliceVisit.rets
				// Step 4
				some aliceForward				
				Alice + MyApp in e3.procs
				EveCode = aliceForward.code
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
				AliceCode in aliceAuth.rets 
				some (aliceAuth.m).redirectTo
				//(aliceInit.m).responseHeaders & Hash in (aliceAuth.m).redirectTo.query
				// Step 3
				some aliceForward
				Alice + MyApp in e2.procs
				AliceCode = aliceForward.code
				// Step 4
				some getToken
				MyApp + Google in e3.procs
		}
*/
	}
} for 1 but 5 Event, 14 Label

run  { 
	some m : Label -> Label | 
		userConstraint[m] and 
		some procs : Event -> Proc, labels : Event -> Label {
			applyMapping[m, procs, labels]	
			behavior[procs, labels]
/*
		some e : Event, id : AppID |  
			myApp_tokens[procs, labels, e, id, AliceToken] 
			and Alice -> e -> id in knows[procs, labels]
*/
		not oauthProperty[procs, labels]
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
				EveCode in eveAuth.rets			
				// Step 3
				some aliceVisit
				e2.procs = AliceBrowser + EvilServer
				EveCode in aliceVisit.rets
				// Step 4
				some aliceForward				
				Alice + MyApp in e3.procs
				EveCode = aliceForward.code
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
				AliceCode in aliceAuth.rets 
				some (aliceAuth.m).redirectTo
//				(aliceInit.m).responseHeaders & Hash in (aliceAuth.m).redirectTo.query
				// Step 3
				some aliceForward
				Alice + MyApp in e2.procs
				AliceCode = aliceForward.code
				// Step 4
				some getToken
				MyApp + Google in e3.procs
		}
*/
	}
} for 1 but 6 Event, 14 Label
