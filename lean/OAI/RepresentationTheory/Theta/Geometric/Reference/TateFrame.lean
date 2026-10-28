import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TateIntegralSpan
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliPoints
import OAI.RepresentationTheory.Theta.Geometric.JointRationalCompletion
import OAI.RepresentationTheory.Theta.Geometric.SplitLocalLattice
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction

/-! # Tate Frame -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The original reference marking constructs a native split Tate
frame and identifies its full integral image with the original local lattice. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

def Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q).symm.trans
    ((LinearEquiv.baseChange ℚ ℚ_[q] _ _ (M.toNativeReferenceModel F).nativeReferenceMarking.symm).trans
      (D.jointRationalCompletion hgood hdegree))

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame_marking (hc : D.HasFiniteCoordinates) (z : ℚ_[q]) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.referenceTateFrame F hgood hdegree
      (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
        (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u)) =
      z • D.jointLocalEmbedding u := by
  change D.jointRationalCompletion hgood hdegree
    ((LinearEquiv.baseChange ℚ ℚ_[q] _ _ (M.toNativeReferenceModel F).nativeReferenceMarking.symm)
      ((AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q).symm (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q _))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
    D.jointRationalCompletion_tmul hgood hdegree hc]

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame_integralPeriod (hc : D.HasFiniteCoordinates) (u : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian) :
    M.referenceTateFrame F hgood hdegree
      (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u)) =
      D.jointLocalEmbedding ((M.toNativeReferenceModel F).nativeReferenceMarking.symm
        (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u)) := by
  have h := M.referenceTateFrame_marking F hgood hdegree hc 1
    ((M.toNativeReferenceModel F).nativeReferenceMarking.symm (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u))
  rw [LinearEquiv.apply_symm_apply, one_smul] at h
  exact h

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame_integral_image (hc : D.HasFiniteCoordinates) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (M.referenceTateFrame F hgood hdegree) = D.jointLocalLattice := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage, Intrinsic.TateIntegralSpan.native_integralTateImage_eq_period_span, Submodule.map_span]
  change Submodule.span ℤ_[q] ((M.referenceTateFrame F hgood hdegree) ''
    Set.range (fun u : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian =>
      AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u))) =
    Submodule.span ℤ_[q] (D.jointLocalEmbedding '' (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)))
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    let v := (M.toNativeReferenceModel F).nativeReferenceMarking.symm (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u)
    refine ⟨v, ?_, (M.referenceTateFrame_integralPeriod F hgood hdegree hc u).symm⟩
    apply ((M.toNativeReferenceModel F).nativeReferenceMarking_integral v).mp
    change (M.toNativeReferenceModel F).nativeReferenceMarking
      ((M.toNativeReferenceModel F).nativeReferenceMarking.symm _) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact u.property
  · rintro ⟨v, hv, rfl⟩
    have hi := ((M.toNativeReferenceModel F).nativeReferenceMarking_integral v).mpr hv
    let u : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian := ⟨((M.toNativeReferenceModel F).nativeReferenceMarking v).val, hi⟩
    refine ⟨AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u),
      Set.mem_range_self u, ?_⟩
    have he : AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion M.abelian u = (M.toNativeReferenceModel F).nativeReferenceMarking v := rfl
    rw [he, M.referenceTateFrame_marking F hgood hdegree hc, one_smul]

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame_integral_mem_iff (hc : D.HasFiniteCoordinates)
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q) :
    u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q ↔
      ∀ v, (M.referenceTateFrame F hgood hdegree u) v ∈ Data.ActiveHeckeThetaData.standardLocalLattice (q := q) := by
  have he : u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q ↔
      M.referenceTateFrame F hgood hdegree u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (M.referenceTateFrame F hgood hdegree) := by
    constructor
    · intro hu
      exact ⟨u, hu, rfl⟩
    · rintro ⟨w, hw, hwu⟩
      exact (M.referenceTateFrame F hgood hdegree).injective hwu ▸ hw
  rw [he, M.referenceTateFrame_integral_image F hgood hdegree hc]
  exact D.jointLocalLattice_standard hg hc hgood _

end

section

/-! Naturality of the original reference Tate coordinates on the
actual rational period generators. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}
    (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTate_linear_ext {V : Type*} [AddCommGroup V] [Module ℚ_[q] V]
    (f g : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q →ₗ[ℚ_[q]] V)
    (h : ∀ z : ℚ_[q], ∀ u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
      f (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
        (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u)) =
      g (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
        (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u))) : f = g := by
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q).surjective w
  induction v using TensorProduct.inductionOn with
  | tmul z u =>
    obtain ⟨a, rfl⟩ := (M.toNativeReferenceModel F).nativeReferenceMarking.surjective u
    exact h z a
  | add u v hu hv => simp only [map_add, hu, hv]

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame_map_marking
    (N : D.PeriodModel hg y) (G : D.ReferenceAnalyticFiber y)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f]
    (t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (ht : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((M.toNativeReferenceModel F).nativeReferenceMarking u) =
      (N.toNativeReferenceModel G).nativeReferenceMarking (t u))
    (z : ℚ_[q]) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    N.referenceTateFrame G hgood hdegree
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f
        (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
          (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u))) =
      z • D.jointLocalEmbedding (t u) := by
  have hn := LinearMap.congr_fun (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality.rationalPeriodTate_natural q f)
    (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, ht] at hn
  rw [hn]
  exact N.referenceTateFrame_marking G hgood hdegree hc z (t u)

end

section

/-! The actual reference Tate frame is equivariant for every original
integral CM endomorphism and the literal split local characters. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame

include hc

theorem Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame_action (a : NumberField.RingOfIntegers E)
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q)
    (v : Fin s × Bool) (i : Fin 3) :
    M.referenceTateFrame F hgood hdegree
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
        (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.action a)) u) v i =
      (D.pel.localCharacter v a : ℚ_[q]) * M.referenceTateFrame F hgood hdegree u v i := by
  let t : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q →ₗ[ℚ_[q]] AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q :=
    LinearMap.pi (fun v => (D.pel.localCharacter v a : ℚ_[q]) • LinearMap.proj v)
  have H : (M.referenceTateFrame F hgood hdegree).toLinearMap.comp
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
        (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.action a))) =
      t.comp (M.referenceTateFrame F hgood hdegree).toLinearMap := by
    apply M.referenceTate_linear_ext F
    intro z w
    change M.referenceTateFrame F hgood hdegree
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
        (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.action a))
        (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
          (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking w))) =
      t (M.referenceTateFrame F hgood hdegree
        (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
          (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking w)))
    rw [M.referenceTateFrame_map_marking F M F hgood hdegree hc
      (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.action a)) (fun u => (a : E) • u)
      ((M.toNativeReferenceModel F).nativeReferenceMarking_action a),
      M.referenceTateFrame_marking F hgood hdegree hc]
    funext v i
    change z * D.localEmbedding v ((a : E) * w i) =
      (D.pel.localCharacter v a : ℚ_[q]) * (z * D.localEmbedding v (w i))
    rw [map_mul, hc.1]
    ring
  exact congrFun (congrFun (LinearMap.congr_fun H u) v) i

end

/-! The actual reference Tate frame is equivariant for every original
integral CM endomorphism and the literal split local characters. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame

def Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame (R : D.ReferencePELPointData hg x) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s R.family.abelian.scheme (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  R.model.referenceTateFrame R.analytic hgood hdegree

include hc

omit hc in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.family_endSchemeMap
    (R : D.ReferencePELPointData hg x) (a : NumberField.RingOfIntegers E) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.family.abelian.scheme (R.family.action a) =
      AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action a) := rfl

omit hc in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.family_rationalTateMap_action
    (R : D.ReferencePELPointData hg x) (a : NumberField.RingOfIntegers E) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
      (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.family.abelian.scheme (R.family.action a)) =
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
      (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap R.model.abelian.toOver (R.model.action a)) := rfl

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.referenceTateFrame_isSplitAction
    (R : D.ReferencePELPointData hg x) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame R.family (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q D.pel.localCharacter
      (R.model.referenceTateFrame R.analytic hgood hdegree) := by
  intro a u v i
  rw [R.family_rationalTateMap_action]
  exact R.model.referenceTateFrame_action R.analytic hgood hdegree hc a u v i

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame_isSplitAction
    (R : D.ReferencePELPointData hg x) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame R.family (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q D.pel.localCharacter
      (R.pelTateFrame hgood hdegree) :=
  R.referenceTateFrame_isSplitAction hgood hdegree hc

end

end OAI.RepresentationTheory.Theta.Geometric
