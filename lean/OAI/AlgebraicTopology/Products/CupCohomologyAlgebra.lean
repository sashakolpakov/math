import OAI.AlgebraicTopology.Products.CupCohomology
import OAI.AlgebraicTopology.Products.Cup

/-! # Cup Cohomology Algebra -/

namespace OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

noncomputable section

/-!
# Associativity and units for the actual cohomology cup product

The degree transports below record equalities of natural-number degrees.
All algebraic laws descend the previously proved laws on actual cochains.
-/

open _root_.CategoryTheory

variable {R : Type} [CommRing R]

/-- Transport of cocycles along equality of cohomological degrees. -/
def cocycleCast (K : SSet.{0}) (M : ModuleCat.{0} R) {m n : ℕ} (h : m = n) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) m →ₗ[R]
      Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) n := by
  subst n
  exact LinearMap.id

/-- Transport in the actual categorical cohomology family. -/
def cohomologyCast (K : SSet.{0}) (M : ModuleCat.{0} R) {m n : ℕ} (h : m = n) :
    (Cohomology.Singular.Basic.simplicialCochains K M).homology m →ₗ[R] (Cohomology.Singular.Basic.simplicialCochains K M).homology n := by
  subst n
  exact LinearMap.id

@[simp]
theorem cocycleCast_val (K : SSet.{0}) (M : ModuleCat.{0} R) {m n : ℕ} (h : m = n)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) m) :
    (cocycleCast K M h c).val = Cup.cochainCast K M h c.val := by
  subst n
  rfl

@[simp]
theorem cohomologyCast_class (K : SSet.{0}) (M : ModuleCat.{0} R)
    {m n : ℕ} (h : m = n) (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) m) :
    cohomologyCast K M h (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K M) m c) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K M) n (cocycleCast K M h c) := by
  subst n
  rfl

/-- Associative coefficient pairings give associative products of cocycles. -/
theorem cocycleCupWith_assoc (K : SSet.{0})
    {M N L P Q T : ModuleCat.{0} R}
    (B₁ : M →ₗ[R] N →ₗ[R] P) (B₂ : P →ₗ[R] L →ₗ[R] T)
    (B₃ : N →ₗ[R] L →ₗ[R] Q) (B₄ : M →ₗ[R] Q →ₗ[R] T)
    (hB : ∀ (x : M) (y : N) (z : L), B₂ (B₁ x y) z = B₄ x (B₃ y z))
    {p q r : ℕ} (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (b : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K L) r) :
    cocycleCast K T (Nat.add_assoc p q r)
      (CupCohomology.cocycleCupWith K B₂ (p + q) r (CupCohomology.cocycleCupWith K B₁ p q a b) c) =
        CupCohomology.cocycleCupWith K B₄ p (q + r) a (CupCohomology.cocycleCupWith K B₃ q r b c) := by
  apply Subtype.ext
  rw [cocycleCast_val]
  exact Cup.cupWith_assoc K B₁ B₂ B₃ B₄ hB a.val b.val c.val

/-- Associativity of the descended product, for arbitrary associative
coefficient pairings. -/
theorem cohomologyCupWith_assoc (K : SSet.{0})
    {M N L P Q T : ModuleCat.{0} R}
    (B₁ : M →ₗ[R] N →ₗ[R] P) (B₂ : P →ₗ[R] L →ₗ[R] T)
    (B₃ : N →ₗ[R] L →ₗ[R] Q) (B₄ : M →ₗ[R] Q →ₗ[R] T)
    (hB : ∀ (x : M) (y : N) (z : L), B₂ (B₁ x y) z = B₄ x (B₃ y z))
    {p q r : ℕ} (a : (Cohomology.Singular.Basic.simplicialCochains K M).homology p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K N).homology q)
    (c : (Cohomology.Singular.Basic.simplicialCochains K L).homology r) :
    cohomologyCast K T (Nat.add_assoc p q r)
      (CupCohomology.cohomologyCupWith K B₂ (p + q) r (CupCohomology.cohomologyCupWith K B₁ p q a b) c) =
        CupCohomology.cohomologyCupWith K B₄ p (q + r) a (CupCohomology.cohomologyCupWith K B₃ q r b c) := by
  obtain ⟨a, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K M) p a
  obtain ⟨b, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K N) q b
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K L) r c
  rw [CupCohomology.cohomologyCupWith_class_class, CupCohomology.cohomologyCupWith_class_class,
    CupCohomology.cohomologyCupWith_class_class, CupCohomology.cohomologyCupWith_class_class, cohomologyCast_class,
    cocycleCupWith_assoc K B₁ B₂ B₃ B₄ hB]

/-- Associativity of the scalar cup product on actual cohomology. -/
theorem cohomologyCup_assoc (K : SSet.{0}) {p q r : ℕ}
    (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology q)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology r) :
    cohomologyCast K (ModuleCat.of R R) (Nat.add_assoc p q r)
      (CupCohomology.cohomologyCup (R := R) K (p + q) r (CupCohomology.cohomologyCup (R := R) K p q a b) c) =
        CupCohomology.cohomologyCup (R := R) K p (q + r) a (CupCohomology.cohomologyCup (R := R) K q r b c) :=
  cohomologyCupWith_assoc K
    (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R)
    (P := ModuleCat.of R R) (Q := ModuleCat.of R R) (T := ModuleCat.of R R)
    (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R) (LinearMap.mul R R)
    (fun x y z => mul_assoc x y z) a b c

/-- The constant-one cochain, with its proved cocycle property. -/
def cocycleCupUnit (K : SSet.{0}) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) 0 :=
  ⟨Cup.cupUnit K, (Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr (Cup.cupUnit_coboundary K)⟩

/-- The degree-zero unit class of the actual cup product. -/
def cohomologyCupUnit (K : SSet.{0}) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology 0 :=
  Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) 0 (cocycleCupUnit K)

/-- The left unit law, with its natural-number degree transport explicit. -/
theorem cohomologyCupUnit_cup (K : SSet.{0}) {p : ℕ}
    (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p) :
    cohomologyCast K (ModuleCat.of R R) (Nat.zero_add p)
      (CupCohomology.cohomologyCup (R := R) K 0 p (cohomologyCupUnit K) a) = a := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p a
  change cohomologyCast K (ModuleCat.of R R) (Nat.zero_add p)
    (CupCohomology.cohomologyCupWith K (LinearMap.mul R R) 0 p
      (Cohomology.Singular.Representatives.cochainClass _ 0 (cocycleCupUnit K)) (Cohomology.Singular.Representatives.cochainClass _ p c)) = Cohomology.Singular.Representatives.cochainClass _ p c
  rw [CupCohomology.cohomologyCupWith_class_class, cohomologyCast_class]
  apply congrArg (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
  apply Subtype.ext
  rw [cocycleCast_val]
  exact Cup.cupUnit_cup K c.val

/-- The right unit law in actual cohomology. -/
@[simp]
theorem cohomologyCup_cupUnit (K : SSet.{0}) {p : ℕ}
    (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p) :
    CupCohomology.cohomologyCup (R := R) K p 0 a (cohomologyCupUnit K) = a := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p a
  change CupCohomology.cohomologyCupWith K (LinearMap.mul R R) p 0
    (Cohomology.Singular.Representatives.cochainClass _ p c) (Cohomology.Singular.Representatives.cochainClass _ 0 (cocycleCupUnit K)) = Cohomology.Singular.Representatives.cochainClass _ p c
  rw [CupCohomology.cohomologyCupWith_class_class]
  apply congrArg (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p)
  apply Subtype.ext
  exact Cup.cup_cupUnit K c.val

/-- The unit of the scalar cup product in genuine singular cohomology. -/
abbrev singularCohomologyCupUnit (X : TopCat.{0}) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X 0 :=
  cohomologyCupUnit (R := R) (TopCat.toSSet.obj X)

end

end OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
