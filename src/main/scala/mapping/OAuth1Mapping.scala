package mapping

import constraints.ImplConstraints
import types.Store

object OAuth1Mapping {
  
  def mapping1 = {
    // abstract and concrete labels
    val authorize = Store.l("authorize")
    val getAccessToken = Store.l("getAccessToken")
    val getRequestToken = Store.l("getRequestToken")    
    
    val initiate = Store.l("initiate")
    val retrieve = Store.l("retrieveReqToken")    
    val authorized = Store.l("authorized")
    
    val authServerPort = Store.l("port_auth_server")
    val clientPort = Store.l("port_client")
         
    // Abstract-concrete label pairs, 
    // each along with user-defined constraints    
    val a2h = new ImplConstraints(authorize, authServerPort)
    a2h.addEqualConstraints(
      Map("req.url.path" -> "path_authorize",
        "req.url.origin" -> "ORIGIN_GOOGLE",
        "req.url.query" -> "userid",   
        //"req.url.query2" -> "reqToken", 
        "req.cookie" -> "none",   
        "req.body" -> "cred",        
        "resp.set_cookie" -> "none",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))
                            
    val ga2h = new ImplConstraints(getAccessToken, authServerPort)
    ga2h.addEqualConstraints(
      Map("req.url.path" -> "path_getAccessToken",
        "req.url.origin" -> "ORIGIN_GOOGLE",
        "req.url.query" -> "reqToken",
        "req.url.query2" -> "none",
        "req.body" -> "none",   
        "req.cookie" -> "none",
        "resp.set_cookie" -> "none",              
        "resp.resource.content" -> "accessToken",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))    
        
    val gr2h = new ImplConstraints(getRequestToken, authServerPort)
    gr2h.addEqualConstraints(
      Map("req.url.path" -> "path_getRequestToken",
        "req.url.origin" -> "ORIGIN_GOOGLE",
        "req.cookie" -> "none",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",        
        "req.body" -> "none",                
        //"resp.resource.content" -> "reqToken",
        //"resp.set_cookie" -> "none",    
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))  
    
    val i2h = new ImplConstraints(initiate, clientPort)   
    i2h.addEqualConstraints(
      Map("req.url.path" -> "path_initiate",
        "req.url.origin" -> "ORIGIN_MYAPP",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",    
        "req.body" -> "none",                
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.set_cookie" -> "session",
        "resp.code" -> "OK"))  
        
    val r2h = new ImplConstraints(retrieve, clientPort) 
    r2h.addEqualConstraints(
      Map("req.url.path" -> "path_retrieve",
        "req.cookie" -> "session",
        "req.url.origin" -> "ORIGIN_MYAPP",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",       
        "req.body" -> "none",                
        "resp.resource.content" -> "reqToken",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",       
        "resp.set_cookie" -> "none",
        "resp.code" -> "OK"))      
        
    val az2h = new ImplConstraints(authorized, clientPort)
    az2h.addEqualConstraints(
      Map("req.url.path" -> "path_authorized",
        "req.url.origin" -> "ORIGIN_MYAPP",
       // "req.url.query" -> "none",
       // "req.url.query2" -> "none",    
        "req.cookie" -> "session",
        "req.body" -> "none",    
        "resp.resource.content" -> "none",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.set_cookie" -> "none",
        "resp.code" -> "OK"))        
        
    new Mapping(Set(a2h, ga2h, gr2h, i2h, az2h, r2h))
  }
  
  def mapping2 = {
    // abstract and concrete labels
    val authorize = Store.l("authorize")
    val getAccessToken = Store.l("getAccessToken")
    val getRequestToken = Store.l("getRequestToken")    
    
    val initiate = Store.l("initiate")
    val retrieve = Store.l("retrieveReqToken")    
    val authorized = Store.l("authorized")
    
    val authServerPort = Store.l("port_auth_server")
    val clientPort = Store.l("port_client")
  
    // Abstract-concrete label pairs, 
    // each along with user-defined constraints    
    val a2h = new ImplConstraints(authorize, authServerPort)
    a2h.addEqualConstraints(
      Map("req.url.path" -> "path_authorize",
        "req.url.origin" -> "ORIGIN_GOOGLE",
        "req.url.query" -> "userid",   
        "req.url.query2" -> "reqToken", 
        "req.cookie" -> "none",   
        "req.body" -> "cred",        
        "resp.set_cookie" -> "none",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))
                            
    val ga2h = new ImplConstraints(getAccessToken, authServerPort)
    ga2h.addEqualConstraints(
      Map("req.url.path" -> "path_getAccessToken",
        "req.url.origin" -> "ORIGIN_GOOGLE",
        "req.url.query" -> "reqToken",
        "req.url.query2" -> "none",
        "req.body" -> "none",                
        "resp.set_cookie" -> "none",              
        "resp.resource.content" -> "accessToken",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))    
        
    val gr2h = new ImplConstraints(getRequestToken, authServerPort)
    gr2h.addEqualConstraints(
      Map("req.url.path" -> "path_getRequestToken",
        "req.url.origin" -> "ORIGIN_GOOGLE",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",        
        "req.body" -> "none",                
        "resp.resource.content" -> "reqToken",
        "resp.set_cookie" -> "none",    
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))  
    
    val i2h = new ImplConstraints(initiate, clientPort)   
    i2h.addEqualConstraints(
      Map("req.url.path" -> "path_initiate",
        "req.url.origin" -> "ORIGIN_MYAPP",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",    
        "req.body" -> "none",                
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.set_cookie" -> "session",
        "resp.code" -> "OK"))  
        
    val r2h = new ImplConstraints(retrieve, clientPort) 
    r2h.addEqualConstraints(
      Map("req.url.path" -> "path_retrieve",
        "req.cookie" -> "session",
        "req.url.origin" -> "ORIGIN_MYAPP",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",       
        "req.body" -> "none",                
        "resp.resource.content" -> "accessToken",
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",     
        "resp.set_cookie" -> "none",
        "resp.code" -> "OK"))      
        
    val az2h = new ImplConstraints(authorized, clientPort)
    az2h.addEqualConstraints(
      Map("req.url.path" -> "path_authorized",
        "req.url.origin" -> "ORIGIN_MYAPP",
        "req.url.query" -> "none",
        "req.url.query2" -> "none",    
        "req.cookie" -> "session",
        "req.body" -> "none",        
        "resp.redirectTo.path" -> "none",
        "resp.redirectTo.origin" -> "none",
        "resp.redirectTo.query" -> "none",
        "resp.redirectTo.query2" -> "none",
        "resp.code" -> "OK"))      
    new Mapping(Set(a2h, ga2h, gr2h, i2h, az2h, r2h))
  }
  
}