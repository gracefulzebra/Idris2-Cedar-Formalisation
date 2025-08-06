module Tests

import CedarLite

-- TEST 1: Basic Entity Equality
-- Source: https://github.com/cedar-policy/cedar/blob/main/README.md
-- ============================

-- Entity store for example
testStoreAliceJane : EntityStore
testStoreAliceJane = ES [
  ("User", "alice", "Alice User"),
  ("Action", "view", "View Action"),  
  ("Album", "jane_vacation", "Jane's Vacation Album"),
  ("Photo", "VacationPhoto94.jpg", "Vacation Photo")
]

-- Context for alice viewing jane's vacation album
testContextAlice : AuthContext (ACS "User" "Action" "Photo" [])
testContextAlice = AC (VERef "User" (VS "Alice User"))
                      (VERef "Action" (VS "View Action"))  
                      (VERef "Photo" (VS "Vacation Photo"))
                      (VStruct [])
                      testStoreAliceJane

-- Policy: permit(principal == User::"alice", action == Action::"view", resource in Album::"jane_vacation")
-- Note: Simplified to test entity equality since we don't have 'in' operator for albums
policyAliceView : Policy (ACS "User" "Action" "Photo" [])
policyAliceView = MkPolicy PERMIT (And 
  (EqualEntity VarPrinciple (ERef "User" (S "alice")))
  (EqualEntity VarAction (ERef "Action" (S "view"))))

-- Test: Alice should be allowed to view per the policy
testAliceView : Decision
testAliceView = auth testContextAlice [policyAliceView]
-- Expected Result: ALLOW

-- Negative test: Different user should be denied
testContextBob : AuthContext (ACS "User" "Action" "Photo" [])  
testContextBob = AC (VERef "User" (VS "Bob User"))
                    (VERef "Action" (VS "View Action"))  
                    (VERef "Photo" (VS "Vacation Photo"))
                    (VStruct [])
                    testStoreAliceJane

testBobView : Decision
testBobView = auth testContextBob [policyAliceView]
-- Expected Result: DENY

-- TEST 2: FORBID OVERRIDES PERMIT
-- Source: https://docs.cedarpolicy.com/auth/authorization.html
-- ============================

-- Policy: forbid all access when context.blocked == true
policyBlockedForbid : Policy (ACS "User" "Action" "Photo" [("blocked", STR)])
policyBlockedForbid = MkPolicy FORBID (EqualString 
  (Dot VarContext "blocked")
  (S "true"))

-- Policy: permit jane to view vacation photo  
policyJanePermit : Policy (ACS "User" "Action" "Photo" [("blocked", STR)])
policyJanePermit = MkPolicy PERMIT (And
  (EqualEntity VarPrinciple (ERef "User" (S "jane")))
  (EqualEntity VarAction (ERef "Action" (S "viewPhoto"))))

-- Context where access is blocked
testContextBlocked : AuthContext (ACS "User" "Action" "Photo" [("blocked", STR)])
testContextBlocked = AC (VERef "User" (VS "jane"))
                        (VERef "Action" (VS "viewPhoto"))  
                        (VERef "Photo" (VS "vacation.jpg"))
                        (VStruct [VF "blocked" (VS "true")])
                        testStoreAliceJane

-- Test: Forbid should override permit
testForbidOverride : Decision  
testForbidOverride = auth testContextBlocked [policyJanePermit, policyBlockedForbid]
-- Expected Result: DENY (forbid overrides permit)

-- Context where access is not blocked
testContextNotBlocked : AuthContext (ACS "User" "Action" "Photo" [("blocked", STR)])
testContextNotBlocked = AC (VERef "User" (VS "jane"))
                           (VERef "Action" (VS "viewPhoto"))  
                           (VERef "Photo" (VS "vacation.jpg"))
                           (VStruct [VF "blocked" (VS "false")])
                           testStoreAliceJane

-- Test: Permit should work when not blocked
testPermitWhenNotBlocked : Decision
testPermitWhenNotBlocked = auth testContextNotBlocked [policyJanePermit, policyBlockedForbid]  
-- Expected Result: ALLOW

-- [ EOF ]