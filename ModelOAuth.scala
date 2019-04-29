/**
 * Representation of the OAuth model
 *
 * Created by: Eunsuk Kang
 */

val OAUTH_ID_GOOGLE = 0
val OAUTH_ID_MYAPP = 1
val OAUTH_ID_ALICE = 2
val OAUTH_ID_EVE = 3

val mtype = Store.d("mtype").asInstanceOf[BasicDatatype];
val oauthID = Store.mkBasicDatatype("OAuthID", mtype);
val oauthCode = Store.mkBasicDatatype("OAuthCode", mtype);
val oauthToken = Store.mkBasicDatatype("OAuthToken", mtype);
val oauthSession = Store.mkBasicDatatype("OAuthSession", mtype);
val oauthCred = Store.mkBasicDatatype("OAuthCred", mtype);

List("id_Alice", "id_Eve").foreach { v => Store.mkValue(v, oauthID) }
List("code_Alice", "code_Eve").foreach { v => Store.mkValue(v, oauthCode) }
List("token_Alice", "token_Eve").foreach { v => Store.mkValue(v, oauthToken) }
List("cred_Alice", "cred_Eve").foreach { v => Store.mkValue(v, oauthCred) }
List("session_X", "session_Y").foreach { v => Store.mkValue(v, oauthSession) }

// OAuth labels (i.e., ports)
val authorize = Store.mkLabel(
  "authorize",
  Map("userid" -> oauthID, "cred" -> oauthCred, "code" -> oauthCode), Set("code"), OAUTH_ID_GOOGLE);
val forward = Store.mkLabel(
  "forward",
  Map("session" -> oauthSession, "code" -> oauthCode), Set[String](), OAUTH_ID_MYAPP);
val initiate = Store.mkLabel(
  "initiate",
  Map("session" -> oauthSession), Set("session"), OAUTH_ID_MYAPP);
val getAccessToken = Store.mkLabel(
  "getAccessToken",
  Map("code" -> oauthCode, "token" -> oauthToken), Set("token"), OAUTH_ID_GOOGLE);

  