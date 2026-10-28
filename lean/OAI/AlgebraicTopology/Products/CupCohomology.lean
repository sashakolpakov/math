import OAI.AlgebraicTopology.Products.CupBoundaries
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # Cup Cohomology -/

namespace OAI.AlgebraicTopology.Products.CupCohomology

noncomputable section

/-!
# The genuine cup product on cohomology

The front/back cup operation is restricted to cocycles and descended through
the actual coboundary submodules. Mathlib's canonical quotient isomorphism
then gives a bilinear operation on its categorical cohomology objects.
Both independence statements use the proved cup-product differential law.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.Representatives

variable {R : Type} [CommRing R]

/-- The cup pairing of two cocycles is a cocycle. -/
theorem cupWith_mem_cocycles (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    Cup.cupWith K B c.val d.val ∈ Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K L) (p + q) := by
  rw [Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Cup.cupWith_coboundary]
  have hc := (Cohomology.Singular.Representatives.mem_cochainCocycles_iff (Cohomology.Singular.Basic.simplicialCochains K M) p c.val).mp c.property
  have hd := (Cohomology.Singular.Representatives.mem_cochainCocycles_iff (Cohomology.Singular.Basic.simplicialCochains K N) q d.val).mp d.property
  rw [hc, hd, Cup.cupWith_zero_left, Cup.cupWith_zero_right, map_zero, smul_zero, add_zero]

/-- The actual bilinear cup operation restricted to the kernels of the outgoing
differentials. -/
def cocycleCupWith (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p →ₗ[R]
      Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q →ₗ[R]
        Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K L) (p + q) where
  toFun c :=
    { toFun d := ⟨Cup.cupWith K B c.val d.val, cupWith_mem_cocycles K B c d⟩
      map_add' d e := Subtype.ext (Cup.cupWith_add_right K B c.val d.val e.val)
      map_smul' r d := Subtype.ext (Cup.cupWith_smul_right K B r c.val d.val) }
  map_add' c e := by
    ext d
    exact Cup.cupWith_add_left K B c.val e.val d.val
  map_smul' r c := by
    ext d
    exact Cup.cupWith_smul_left K B r c.val d.val

@[simp]
theorem cocycleCupWith_val (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    (cocycleCupWith K B p q c d).val = Cup.cupWith K B c.val d.val := rfl

/-- The cohomology class of the cup product of cocycles, before descending its
two arguments to cohomology. -/
def cocycleCupClass (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p →ₗ[R]
      Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q →ₗ[R]
        (Cohomology.Singular.Basic.simplicialCochains K L).homology (p + q) :=
  (cocycleCupWith K B p q).compr₂ (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K L) (p + q))

@[simp]
theorem cocycleCupClass_apply (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    cocycleCupClass K B p q c d =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K L) (p + q) (cocycleCupWith K B p q c d) := rfl

/-- A coboundary in the first argument gives zero cohomology class. -/
theorem cocycleCupClass_boundary_left (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ)
    (b : ((Cohomology.Singular.Basic.simplicialCochains K M).sc p).X₁)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    cocycleCupClass K B p q (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.Basic.simplicialCochains K M) p b) d = 0 := by
  rw [cocycleCupClass_apply, Cohomology.Singular.Representatives.cochainClass_eq_zero_iff]
  obtain ⟨z, hz⟩ := CupBoundaries.cupWith_boundary_left K B p q b d
  exact ⟨z, Subtype.ext hz⟩

/-- A coboundary in the second argument gives zero cohomology class. -/
theorem cocycleCupClass_boundary_right (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (b : ((Cohomology.Singular.Basic.simplicialCochains K N).sc q).X₁) :
    cocycleCupClass K B p q c (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.Basic.simplicialCochains K N) q b) = 0 := by
  rw [cocycleCupClass_apply, Cohomology.Singular.Representatives.cochainClass_eq_zero_iff]
  obtain ⟨z, hz⟩ := CupBoundaries.cupWith_boundary_right K B p q c b
  exact ⟨z, Subtype.ext hz⟩

/-- The front/back cup product on mathlib's actual cohomology objects, with
arbitrary bilinear coefficients. -/
def cohomologyCupWith (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) (p q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K M).homology p →ₗ[R]
      (Cohomology.Singular.Basic.simplicialCochains K N).homology q →ₗ[R]
        (Cohomology.Singular.Basic.simplicialCochains K L).homology (p + q) :=
  (((cocycleCupClass K B p q).liftQ₂
    (Cohomology.Singular.Representatives.cochainBoundaries (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (Cohomology.Singular.Representatives.cochainBoundaries (Cohomology.Singular.Basic.simplicialCochains K N) q)
    (by
      rintro c ⟨b, rfl⟩
      apply LinearMap.ext
      intro d
      exact cocycleCupClass_boundary_left K B p q b d)
    (by
      rintro d ⟨b, rfl⟩
      apply LinearMap.ext
      intro c
      exact cocycleCupClass_boundary_right K B p q c b)).comp
    (Cohomology.Singular.Representatives.cohomologyQuotientIso (Cohomology.Singular.Basic.simplicialCochains K M) p).toLinearEquiv.toLinearMap).compl₂
      (Cohomology.Singular.Representatives.cohomologyQuotientIso (Cohomology.Singular.Basic.simplicialCochains K N) q).toLinearEquiv.toLinearMap

/-- The descended product is represented by the actual cup of any two cocycle
representatives. -/
@[simp]
theorem cohomologyCupWith_class_class (K : SSet.{0}) {M N L : ModuleCat.{0} R}
    (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K M) p)
    (d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K N) q) :
    cohomologyCupWith K B p q
      (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K M) p c)
      (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K N) q d) =
        Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K L) (p + q) (cocycleCupWith K B p q c d) := by
  simp only [cohomologyCupWith, Cohomology.Singular.Representatives.cochainClass, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- The scalar cup product in actual simplicial cohomology. -/
abbrev cohomologyCup (K : SSet.{0}) (p q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p →ₗ[R]
      (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology q →ₗ[R]
        (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology (p + q) :=
  cohomologyCupWith K (LinearMap.mul R R) p q

/-- The usual scalar cup product on genuine singular cohomology. -/
abbrev singularCohomologyCup (X : TopCat.{0}) (p q : ℕ) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p →ₗ[R]
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q →ₗ[R]
        Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + q) :=
  cohomologyCup (TopCat.toSSet.obj X) p q

/-- Singular cup classes are represented by the ordinary singular cochain
front/back product. -/
@[simp]
theorem singularCohomologyCup_class_class (X : TopCat.{0}) {p q : ℕ}
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (d : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X q) :
    singularCohomologyCup (R := R) X p q (Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X p c)
      (Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X q d) =
        Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X (p + q)
          (cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul R R) p q c d) :=
  cohomologyCupWith_class_class (M := ModuleCat.of R R) (N := ModuleCat.of R R)
    (L := ModuleCat.of R R) (TopCat.toSSet.obj X) (LinearMap.mul R R) c d

end

end OAI.AlgebraicTopology.Products.CupCohomology
