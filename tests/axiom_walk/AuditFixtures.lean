namespace AuditFixtures

axiom forbiddenNat : Nat
noncomputable def pick : Nat := forbiddenNat

structure S9 where
  x : Fin (pick + 1)

mutual
inductive M1 where
  | mk : Fin (pick + 1) → M2 → M1
inductive M2 where
  | mk : M1 → M2
end

axiom forbiddenProof : False
theorem wrapped : True := False.elim forbiddenProof
noncomputable opaque hidden : Nat := forbiddenNat

private axiom privateNat : Nat
noncomputable def throughPrivate : Nat := privateNat

end AuditFixtures
