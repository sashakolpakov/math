import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineGenericRank
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineFiberDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicEtale

/-! # Intrinsic Fiber Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A commuting square of injections identifies a fiber whenever the
source injection covers that fiber. -/
def fiberEquiv_of_commuting_square
    {P Q M N : Type*} (f : M → N) (a : P → M) (b : Q → N) (g : P → Q)
    (hsquare : ∀ p, f (a p) = b (g p))
    (ha : Function.Injective a) (hb : Function.Injective b) (q : Q)
    (hcover : f ⁻¹' {b q} ⊆ Set.range a) :
    {p : P // g p = q} ≃ {x : M // f x = b q} := by
  let t : {p : P // g p = q} → {x : M // f x = b q} :=
    fun p => ⟨a p.val, (hsquare p.val).trans (congrArg b p.property)⟩
  apply Equiv.ofBijective t
  constructor
  · intro p p' h
    exact Subtype.ext (ha (congrArg Subtype.val h))
  · intro x
    obtain ⟨p, hp⟩ := hcover x.property
    have hgp : g p = q := hb ((hsquare p).symm.trans (hp ▸ x.property))
    exact ⟨⟨p, hgp⟩, Subtype.ext hp⟩

/-- Actual scheme-point fibers agree with fibers of the affine algebra
pullback on a target affine neighborhood. -/
def nativeAffineFiberEquiv
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (φ : X ⟶ Y) [IsAffineHom φ.left]
    (V : Y.left.Opens) (hV : IsAffineOpen V)
    (q : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)) :
    {p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V)) //
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V) p = q} ≃
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV q} := by
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  apply fiberEquiv_of_commuting_square (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X W hW)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV)
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V))
    (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW)
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap _ _).injective
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap _ _).injective q
  intro x hx
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
  have hr : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV) := ⟨q, hx.symm⟩
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  exact hr

/-- For a dominant finite etale morphism of integral complex schemes,
each actual complex fiber has size equal to its generic residue degree. -/
theorem native_fiber_card_eq_residueDegree
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    (φ : X ⟶ Y) [IsFinite φ.left] [Etale φ.left]
    (hη : φ.left (genericPoint X.left) = genericPoint Y.left)
    (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    Nat.card {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x = y} =
      φ.left.residueDegree (genericPoint X.left) := by
  obtain ⟨V, hV, q, hq⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift Y y
  have hyV : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y ∈ V := by
    have hr : y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV) := ⟨q, hq⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  have hηV : genericPoint Y.left ∈ V :=
    ((genericPoint_spec Y.left).mem_open_set_iff V.isOpen).mpr (by
      simpa using (show (V : Set Y.left).Nonempty from ⟨_, hyV⟩))
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  have hηW : genericPoint X.left ∈ W := by
    change φ.left (genericPoint X.left) ∈ V
    rw [hη]
    exact hηV
  let : Nonempty V := ⟨⟨genericPoint Y.left, hηV⟩⟩
  let : Nonempty W := ⟨⟨genericPoint X.left, hηW⟩⟩
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V
  let B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X W
  let : IsDomain A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain Y V
  let h : A →ₐ[ℂ] B := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V
  have hf : h.toRingHom.Finite := φ.left.finite_app V hV
  have he : h.toRingHom.Etale := IntrinsicEtale.Constructions.Construction.nativeAffineOpenPullback_etale φ V hV
  rw [← hq]
  calc
    _ = Nat.card {p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B // Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h p = q} :=
      (Nat.card_congr (nativeAffineFiberEquiv φ V hV q)).symm
    _ = @Module.finrank A B _ _ h.toRingHom.toAlgebra.toModule :=
      AffineFiberDegree.Constructions.Construction.card_affineEtale_fiber h hf he q
    _ = φ.left.residueDegree (genericPoint X.left) := by
      have hr := AffineGenericRank.Constructions.Construction.residueDegree_eq_affine_rank φ.left hη V W le_rfl hV hW hηV hηW
      change @Module.finrank Γ(Y.left, V) Γ(X.left, W) _ _
        (φ.left.app V).hom.toAlgebra.toModule = _
      rw [φ.left.app_eq_appLE]
      exact hr.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction
