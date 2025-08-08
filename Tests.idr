module Tests

import CedarLite

-- TEST 1: Basic Entity Equality
-- Source: https://github.com/cedar-policy/cedar/blob/main/README.md
-- ============================

testStoreAliceJane : EntityStore
testStoreAliceJane = ES [
  ("User", "alice", "Alice User"),
  ("Action", "view", "View Action"),  
  ("Album", "jane_vacation", "Jane's Vacation Album"),
  ("Photo", "VacationPhoto94.jpg", "Vacation Photo")
]

testContextAlice : AuthContext (ACS "User" "Action" "Photo" [])
testContextAlice = AC (VERef "User" (VS "Alice User"))
                      (VERef "Action" (VS "View Action"))  
                      (VERef "Photo" (VS "Vacation Photo"))
                      (VStruct [])
                      testStoreAliceJane

policyAliceView2 : Policy (ACS "User" "Action" "Photo" [])
policyAliceView2 = MkPolicy PERMIT 
  (EqualEntity VarPrinciple (ERef "User" (S "alice")))  
  (EqualEntity VarAction (ERef "Action" (S "view")))    
  (B True)                                              
  []                                                    

-- Test: Alice should be allowed to vieww
testAliceView2 : Decision
testAliceView2 = auth testContextAlice [policyAliceView2]
-- Expected Result: ALLOW

-- Negative test: Different user should be denied
testContextBob : AuthContext (ACS "User" "Action" "Photo" [])  
testContextBob = AC (VERef "User" (VS "Bob User"))
                    (VERef "Action" (VS "View Action"))  
                    (VERef "Photo" (VS "Vacation Photo"))
                    (VStruct [])
                    testStoreAliceJane

testBobView2 : Decision
testBobView2 = auth testContextBob [policyAliceView2]
-- Expected Result: DENY

-- TEST 2: FORBID OVERRIDES PERMIT
-- Source: https://docs.cedarpolicy.com/auth/authorization.html
-- ============================

policyBlockedForbid2 : Policy (ACS "User" "Action" "Photo" [("blocked", STR)])
policyBlockedForbid2 = MkPolicy FORBID
  (B True)                                              
  (B True)                                               
  (B True)                                              
  [EqualString (Dot VarContext "blocked") (S "true")]  

policyJanePermit2 : Policy (ACS "User" "Action" "Photo" [("blocked", STR)])
policyJanePermit2 = MkPolicy PERMIT
  (EqualEntity VarPrinciple (ERef "User" (S "jane")))   
  (EqualEntity VarAction (ERef "Action" (S "viewPhoto"))) 
  (B True)                                              
  []                                                   

-- Context where access is blocked
testContextBlocked : AuthContext (ACS "User" "Action" "Photo" [("blocked", STR)])
testContextBlocked = AC (VERef "User" (VS "jane"))
                        (VERef "Action" (VS "viewPhoto"))  
                        (VERef "Photo" (VS "vacation.jpg"))
                        (VStruct [VF "blocked" (VS "true")])
                        testStoreAliceJane

-- Test: Forbid overide permit
testForbidOverride2 : Decision  
testForbidOverride2 = auth testContextBlocked [policyJanePermit2, policyBlockedForbid2]
-- Expected Result: DENY (forbid overrides permit)

testContextNotBlocked : AuthContext (ACS "User" "Action" "Photo" [("blocked", STR)])
testContextNotBlocked = AC (VERef "User" (VS "jane"))
                           (VERef "Action" (VS "viewPhoto"))  
                           (VERef "Photo" (VS "vacation.jpg"))
                           (VStruct [VF "blocked" (VS "false")])
                           testStoreAliceJane

-- Test: Permit should work when not blocked
testPermitWhenNotBlocked2 : Decision
testPermitWhenNotBlocked2 = auth testContextNotBlocked [policyJanePermit2, policyBlockedForbid2]  
-- Expected Result: ALLOW

-- TEST 3: Explicit Policy Creation
-- ============================

-- Test permit all policy (explicit)
testPermitAll : Decision
testPermitAll = auth testContextAlice [MkPolicy PERMIT (B True) (B True) (B True) []]
-- Expected Result: ALLOW

-- Test permit specific principal policy (explicit)
testPermitPrincipalAlice : Decision
testPermitPrincipalAlice = auth testContextAlice [MkPolicy PERMIT 
                                                     (EqualEntity VarPrinciple (ERef "User" (S "alice")))
                                                     (B True) 
                                                     (B True) 
                                                     []]
-- Expected Result: ALLOW

-- TEST 4: Complex Policy with Multiple When Conditions
-- ============================

complexPolicy2 : Policy (ACS "User" "Action" "Photo" [("department", STR), ("clearance", STR)])
complexPolicy2 = MkPolicy PERMIT
  (EqualEntity VarPrinciple (ERef "User" (S "alice"))) 
  (EqualEntity VarAction (ERef "Action" (S "view")))     
  (B True)                                              
  [ EqualString (Dot VarContext "department") (S "security"),  
    EqualString (Dot VarContext "clearance") (S "high") ]    

testContextHighClearance : AuthContext (ACS "User" "Action" "Photo" [("department", STR), ("clearance", STR)])
testContextHighClearance = AC (VERef "User" (VS "alice"))
                               (VERef "Action" (VS "view"))  
                               (VERef "Photo" (VS "classified.jpg"))
                               (VStruct [VF "department" (VS "security"), VF "clearance" (VS "high")])
                               testStoreAliceJane

testComplexPolicy2 : Decision
testComplexPolicy2 = auth testContextHighClearance [complexPolicy2]
-- Expected Result: ALLOW

testContextLowClearance : AuthContext (ACS "User" "Action" "Photo" [("department", STR), ("clearance", STR)])
testContextLowClearance = AC (VERef "User" (VS "alice"))
                              (VERef "Action" (VS "view"))  
                              (VERef "Photo" (VS "classified.jpg"))
                              (VStruct [VF "department" (VS "security"), VF "clearance" (VS "low")])
                              testStoreAliceJane

testComplexPolicyDeny2 : Decision
testComplexPolicyDeny2 = auth testContextLowClearance [complexPolicy2]
-- Expected Result: DENY

-- TEST 5: Singleton Type Integration with Bool
-- ============================

-- Policy using EqualSelf which returns TRUE singleton type
policySingletonTrue : Policy (ACS "User" "Action" "Photo" [])
policySingletonTrue = MkPolicy PERMIT 
  (Convert TB (EqualSelf VarPrinciple))  -- Convert TRUE to BOOL
  (B True)                               
  (B True)                               
  []

-- Test: TRUE singleton should work with And
testSingletonTrue : Decision
testSingletonTrue = auth testContextAlice [policySingletonTrue]
-- Expected Result: ALLOW

-- Policy mixing TRUE singleton types
policySingletonMixed : Policy (ACS "User" "Action" "Photo" [])
policySingletonMixed = MkPolicy PERMIT
  (Convert TB (EqualSelf VarPrinciple))  -- Convert TRUE to BOOL
  (Convert TB (EqualSelf VarAction))      
  (Convert TB (EqualSelf VarResource))   
  []

-- Test: Multiple TRUE singletonsall convert properly
testSingletonMixed : Decision  
testSingletonMixed = auth testContextAlice [policySingletonMixed]
-- Expected Result: ALLOW

-- [ EOF ]