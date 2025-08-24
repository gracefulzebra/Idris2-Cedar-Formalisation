module Tests

import CedarLite

-- TEST 1: Basic Entity Equality
-- Source: https://github.com/cedar-policy/cedar/blob/main/README.md
-- ============================

store : EntityStore  
store = ES [
  ("User", "alice", "alice"),
  ("Action", "view", "view"),
  ("Album", "vacation", "vacation")
]

policy : Policy (ACS "User" "Action" "Album" [])
policy = MkPolicy PERMIT
  (EqualEntity VarPrinciple (ERef "User" (S "alice")))
  (EqualEntity VarAction (ERef "Action" (S "view")))  
  (EqualEntity VarResource (ERef "Album" (S "vacation")))
  []

aliceContext : AuthContext (ACS "User" "Action" "Album" [])
aliceContext = AC
  (VERef "User" (VS "alice"))
  (VERef "Action" (VS "view"))
  (VERef "Album" (VS "vacation"))
  (VStruct [])
  store

testAlice : Decision
testAlice = auth aliceContext [policy]
-- Expected: ALLOW
 
bobContext : AuthContext (ACS "User" "Action" "Album" [])
bobContext = AC
  (VERef "User" (VS "bob"))
  (VERef "Action" (VS "view"))
  (VERef "Album" (VS "vacation"))
  (VStruct [])
  store

testBob : Decision  
testBob = auth bobContext [policy]
-- Expected: DENY

-- TEST 2: When Clause and Dot Op Testing (From Policy 4)
-- Source: https://docs.cedarpolicy.com/auth/authorization.html
-- =============================================================================
testStoreP4 : EntityStore
testStoreP4 = ES [
  ("User", "jane", "jane"),
  ("Action", "viewPhoto", "viewPhoto"), 
  ("Action", "updateTags", "updateTags"),
  ("Photo", "vacation.jpg", "vacation.jpg")
]

policyP4Test : Policy (ACS "User" "Action" "Photo" [("owner", STR)])
policyP4Test = MkPolicy PERMIT
  (B True)
  (EqualEntity VarAction (ERef "Action" (S "updateTags")))
  (B True)
  [EqualString (Dot VarContext "owner") (S "jane")]

testContextP4Fail : AuthContext (ACS "User" "Action" "Photo" [("owner", STR)])
testContextP4Fail = AC
  (VERef "User" (VS "jane"))
  (VERef "Action" (VS "viewPhoto"))
  (VERef "Photo" (VS "vacation.jpg"))
  (VStruct [VF "owner" (VS "jane")])
  testStoreP4

testContextP4Success : AuthContext (ACS "User" "Action" "Photo" [("owner", STR)])
testContextP4Success = AC
  (VERef "User" (VS "jane"))
  (VERef "Action" (VS "updateTags"))
  (VERef "Photo" (VS "vacation.jpg"))
  (VStruct [VF "owner" (VS "jane")])
  testStoreP4

testP4PolicyFail : Decision
testP4PolicyFail = auth testContextP4Fail [policyP4Test]
-- Expected: DENY

testP4PolicySuccess : Decision
testP4PolicySuccess = auth testContextP4Success [policyP4Test]
-- Expected: ALLOW


-- [ EOF ]