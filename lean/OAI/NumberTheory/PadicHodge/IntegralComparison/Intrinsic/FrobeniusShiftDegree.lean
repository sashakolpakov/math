import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.FrobeniusShiftEtale
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.IntegerPolynomialNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatGenericDegree

/-! # Frobenius Shift Degree -/

namespace OAI.NumberTheory.PadicHodge

noncomputable section

/-! The native integer Frobenius polynomial computes the actual
finite-flat rank of [n]+F on the original special fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

attribute [local instance] GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_group GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_commutative
  GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_proper GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_smooth GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_integral

local instance GeometricComparison.Geometry.AbelianH1Model.special_geometricallyIntegral : GeometricallyIntegral A.specialFiber.scheme.hom :=
  A.specialFiber_geometricallyIntegral

local instance GeometricComparison.Geometry.AbelianH1Model.special_integral : IsIntegral A.specialFiber.scheme.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.specialFiber.scheme.hom

local instance GeometricComparison.Geometry.AbelianH1Model.geometric_integral : IsIntegral A.geometricSpecialFiber.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.geometricSpecialFiber.hom

theorem GeometricComparison.Geometry.AbelianH1Model.nativeFrobeniusShift_finite_etale (n : ℕ) (hn : ¬q ∣ n) :
    IsFinite (((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left) ∧
    Surjective (((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left) ∧
    AlgebraicGeometry.Etale (((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left) :=
  IntegralComparison.Reference.FrobeniusShiftEtale.finite_etale (ZMod q) A.specialFiber.scheme n
    (fun h => hn ((ZMod.natCast_eq_zero_iff _ _).mp h))

theorem GeometricComparison.Geometry.AbelianH1Model.nativeFrobeniusShift_geometric (n : ℕ) :
    ((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius).toMul.hom.hom.left =
    OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberMap (ZMod q) (((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom) := by
  let φ : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme →+* OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber :=
    OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange (ZMod q) A.specialFiber.scheme
  have hn : φ (n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) =
      (n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) := map_natCast φ n
  have h : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange (ZMod q) A.specialFiber.scheme
      ((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) + OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme) =
    (n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius := by
    exact (φ.map_add (n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme)
      (OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme)).trans
        (congrArg (fun z : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber => z + A.nativeGeometricFrobenius) hn)
  exact (congrArg (fun z : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber => z.toMul.hom.hom.left) h).symm

theorem GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_eval_neg_nat_finrank
    (n : ℕ) (hn : ¬q ∣ n) (x : A.specialFiber.scheme.left) :
    A.nativeIntegerFrobeniusPolynomial.eval (-(n : ℤ)) =
      ((((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
        OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left.finrank x) : ℤ) := by
  let f := ((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
    OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom
  let g := ((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius).toMul.hom.hom
  obtain ⟨hfin, hsurj, het⟩ := A.nativeFrobeniusShift_finite_etale n hn
  let : IsFinite f.left := hfin
  let : Surjective f.left := hsurj
  let : AlgebraicGeometry.Etale f.left := het
  let p := pullback.fst A.specialFiber.scheme.hom (OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))
  have hp : IsPullback p g.left f.left p := by
    change IsPullback p
      (((n : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber) + A.nativeGeometricFrobenius).toMul.hom.hom.left)
      f.left p
    rw [A.nativeFrobeniusShift_geometric n]
    exact (OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapBaseChange.Construction.geometricFiberMap_isPullback (ZMod q) f).flip
  let : IsFinite g.left := MorphismProperty.of_isPullback (P := @IsFinite) hp inferInstance
  let : Surjective g.left := MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance
  let : AlgebraicGeometry.Etale g.left :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) hp inferInstance
  have hnormal (y : A.geometricSpecialFiber.left) :
      IsIntegrallyClosed (A.geometricSpecialFiber.left.presheaf.stalk y) := by
    have := OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.geometricSpecialFiber.hom y
    infer_instance
  have hd : g.left.residueDegree (genericPoint A.geometricSpecialFiber.left) = f.left.finrank x := by
    rw [← IntegralComparison.Finite.FlatGenericDegree.finiteFlat_finrank_generic_eq_residueDegree g.left hnormal,
      Scheme.Hom.finrank_of_isPullback p g.left f.left p hp]
    exact f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
  exact (A.nativeIntegerFrobeniusPolynomial_eval_neg_nat n).trans (congrArg (fun d : ℕ => (d : ℤ)) hd)

end

end OAI.NumberTheory.PadicHodge
