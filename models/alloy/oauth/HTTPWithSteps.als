/**
	* HTTP.als
	* Generic model of interaction between HTTP server and browser
	*/
module HTTPWithSteps

open util/ordering[Event] as EO

open util/ordering[Step] as SO

abstract sig Step {
	e : Event
}
fact {
	all s1, s2 : Step |
		s1 -> s2 in SO/next iff
			s1.e -> s2.e in EO/next
}

abstract sig Event {
	sender, receiver : set Proc
}
abstract sig Proc {}

/** 
	Data flow model
*/
abstract sig Module extends Proc {
	owns : set Data
}
abstract sig DataflowLabel extends Event {
	args : set Data,
	rets : set Data
}

abstract sig Data {
//	flds : set Data
}

/**
	* Datatypes related to HTTP requests
	*/
// web resources
abstract sig WebResource {
	content : set Content
}

sig Content in Data {}
abstract sig HTML extends WebResource {
//	links : set URL,			// links that trigger other HTTP requests	
	tags : set Tag
}{
	content = tags
//	links + tags in flds
}

// HTML tags
sig Tag in Data {}
abstract sig Media extends WebResource {} 		// image files, etc.

// protocols -- HTTP vs HTTPS
abstract sig StatusCode {}
one sig INVALID, REDIRECT, OK extends StatusCode {}

abstract sig Protocol {}
one sig ProcHTTP, ProcHTTPS extends Protocol {}
abstract sig IP {}
abstract sig Host extends IP {}
abstract sig Port {}
abstract sig Path {}
sig Query in Data {}


// request headers
sig Header in Data {}

// optional payload in the body 
sig Payload in Data {}

// Origin is like URL, except it doesn't include port
abstract sig Origin {
	protocol : Protocol,
	host : Host,
	port : lone Port
}

fact OriginsAreCanonical {
	no disj o1, o2 : Origin {
		o1.protocol = o2.protocol
		o1.host = o2.host
		o1.port = o2.port
	}
}	

/**
	* A model of an HTTP server 
	*/
abstract sig Server extends Endpoint {
	host : Host,
//	resources : URL -> Resource	-- maps each URL to some resource
}{
	host = addr	
/*
	// only accepts requests with the same host as the server
	all o : this.receives[HTTPReq] {
		o.url.origin.@host = host 
	}

	// only returns resource to which the URL is mapped to
	all o : this.receives[HTTPReq] | {
		o.resource in resources[o.url]
	}
*/
	// all URLs have the same domain
//	all u : resources.Resource | u.origin.@host = host	

	// initially only has access to resources that it stores
	//no owns & (WebResource - resources[URL])
}


abstract sig Endpoint extends Module {
	addr : lone IP
}

/** 
	* A model of a browser
	*/
abstract sig Browser extends Endpoint {
	// frames that this browser currently contains
	//	frames : Frame -> Event
}{
/*
	all f : Frame, o : Op |
		f -> o in frames implies 
			// every frame that the browser stores must be the respones of some HTTP request
			// that this browser has already sent
			some o2 : this.hasSent[o, HTTPReq] {
				f.origin = o2.url.origin
				f.path = o2.url.path
				f.originalContent = o2.resource
			}
*/
}

/*
abstract sig Frame {
	// current content of this frame
	content : HTML lone -> Event,
	// the original content, from the HTTP server that stored it
	originalContent : HTML,
	// host & path & port from which the frame originated
	origin : Origin,
	path : lone Path
}
*/

/**
	* HTTP request operation
	*/


sig HTTPReq in DataflowLabel {
	// URL consists of a protocol, a host, an optional port, and an optional path, and a set of query data
	url_origin : Origin,
	url_path : lone Path,
	url_query,url_query2 : lone Query,
	cookie : lone Header,
	body : lone Payload,
	// response of the request
	resp_code : lone StatusCode,
	resp_set_cookie : lone Header,
	resp_redirectTo_origin : lone Origin,
	resp_redirectTo_path : lone Path,
	resp_redirectTo_query : lone Query,
	resp_redirectTo_query2 : lone Query,
	resp_resource : lone WebResource
}{
	args = url_query + url_query2 + cookie + body
	rets = resp_set_cookie +	resp_resource.content +
		resp_redirectTo_query + resp_redirectTo_query2
	
	some sender & (Server + Browser)
	some receiver & Server
}


sig UserReq in HTTPReq {}{
	sender in Browser
}
sig RedirectReq in HTTPReq {
	trigger : HTTPReq
}

fact { 
	no UserReq & RedirectReq
}

sig GET, POST, PUT in HTTPReq {}
fact {
	no GET & POST 
	no POST & PUT 
	no PUT & GET
}

sig Cookie in Header {
	origin : Origin
}
sig SetCookie in Header {
	set_origin : Origin
}

// Security assumptions
fact Assumptions {
	// Distinct browsers can't share a frame
	// no disj b1, b2 : Browser | some b1.frames & b2.frames
}

-- auxiliary stuff
fun WebBasicData : set univ {
	Query + Header + Payload + Tag + Content 
}

run { 
} for 4

