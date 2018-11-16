package model

import types.BasicDatatype
import types.Store

object ModelHttp2 {
  
  val AUTH_SERVER_ID = 0
  val CLIENT_SERVER_ID = 1
  val ATTACKER_SERVER_ID = 2 
  
  def make = {
    
    // Type declarations
    val mtype = Store.d("mtype").asInstanceOf[BasicDatatype];
        
    val httpStatusCode = Store.mkBasicDatatype("HttpStatusCode");
    val path = Store.mkBasicDatatype("Path");
    val origin = Store.mkBasicDatatype("Origin");
    val resource = Store.mkComplexDatatype("Resource", Map("content" -> mtype));
    val url = Store.mkComplexDatatype("URL", Map(
      "origin" -> origin, 
      "path" -> path,
      "query" -> mtype,
      "query2" -> mtype));
     val httpReq = Store.mkComplexDatatype("Req",  Map(
      "url" -> url,
      "cookie" -> mtype,
      "body" -> mtype)); 
    val httpResp = Store.mkComplexDatatype("Resp", Map(
      "code" -> httpStatusCode, 
      "set_cookie" -> mtype,
      "redirectTo" -> url,
      "resource" -> resource));        
    
    // List of values in datatypes
    List("path_authorize", "path_getAccessToken", "path_getRequestToken",
      "path_initiate", "path_authorized", "path_retrieve").foreach { v => Store.mkValue(v, path) };
    List("ORIGIN_GOOGLE", "ORIGIN_ATTACKER", "ORIGIN_MYAPP").foreach { v => Store.mkValue(v, origin) };  
    List("OK", "REDIRECT", "INVAID").foreach{ v => Store.mkValue(v, httpStatusCode) };
    
    // Labels (i.e., ports in the SPIN model)
    val httpPortA = Store.mkLabel("port_auth_server", Map("req" -> httpReq, "resp" -> httpResp), Set("resp"), AUTH_SERVER_ID,
        Map("req" -> "reqs[sender_id]", "resp" -> ("resps[" + AUTH_SERVER_ID + "]")));
    val httpPortB = Store.mkLabel("port_client", Map("req" -> httpReq, "resp" -> httpResp), Set("resp"), CLIENT_SERVER_ID,
        Map("req" -> "reqs[sender_id]", "resp" -> ("resps[" + CLIENT_SERVER_ID + "]"))); 
    val httpPortC = Store.mkLabel("port_attacker", Map("req" -> httpReq, "resp" -> httpResp), Set("resp"), ATTACKER_SERVER_ID,
        Map("req" -> "reqs[sender_id]", "resp" -> ("resps[" + ATTACKER_SERVER_ID + "]"))); 
    
  }
}