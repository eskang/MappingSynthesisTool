package model

import types.BasicDatatype
import types.Store

object ModelOAuth1 {
     
  val OAUTH_ID_GOOGLE = 0
  val OAUTH_ID_MYAPP = 1
  val OAUTH_ID_ALICE = 2
  val OAUTH_ID_EVE = 3
  
  def make = {    
    
    val mtype = Store.d("mtype").asInstanceOf[BasicDatatype];
    val oauthID = Store.mkBasicDatatype("OAuthID", mtype);
    val reqToken = Store.mkBasicDatatype("ReqToken", mtype);
    val accessToken = Store.mkBasicDatatype("AccessToken", mtype);
    val oauthSession = Store.mkBasicDatatype("OAuthSession", mtype);
    val oauthCred = Store.mkBasicDatatype("OAuthCred", mtype);
    
    List("idAlice", "idEve").foreach { v => Store.mkValue(v, oauthID) }
    List("requestTokenA", "requestTokenB").foreach { v => Store.mkValue(v, reqToken) }
    List("accessTokenAlice", "accessTokenEve").foreach { v => Store.mkValue(v, accessToken) }
    List("credAlice", "credEve").foreach { v => Store.mkValue(v, oauthCred) }
    List("sessionX", "sessionY").foreach{ v => Store.mkValue(v, oauthSession) }
      
    // OAuth labels (i.e., ports)
    val authorize = Store.mkLabel("authorize", 
        Map( "userid" -> oauthID, "cred" -> oauthCred, "reqToken" -> reqToken), Set[String](), OAUTH_ID_GOOGLE);
    val getReqToken = Store.mkLabel("getRequestToken", 
        Map("reqToken" -> reqToken), Set("reqToken"), OAUTH_ID_GOOGLE);
    val getAccessToken = Store.mkLabel("getAccessToken", 
        Map("reqToken" -> reqToken, "accessToken" -> accessToken), Set("accessToken"), OAUTH_ID_GOOGLE);
    
    val initiate = Store.mkLabel("initiate", 
        Map("session" -> oauthSession), Set("session"), OAUTH_ID_MYAPP); 
    val retrieve = Store.mkLabel("retrieveReqToken", 
        Map("session" -> oauthSession, "reqToken" -> reqToken),  Set("reqToken"), OAUTH_ID_MYAPP); 
    val authorized = Store.mkLabel("authorized", 
        Map("session" -> oauthSession), Set[String](), OAUTH_ID_MYAPP);
  }
  
}