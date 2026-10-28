import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: global specialization of an integral scheme

The actual global parameter gives a finite effective divisor on the integral
Noetherian deformation. Its entire support lies on the scheme-theoretic zero
fiber, so that divisor defines a finite cycle on the glued normal cone.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Order
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- The coordinate section on the parameter line. -/
def parameterLineSection : Γ(Deformation.Parameter.BundleCycles.deformationParameterLine.{u}, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X

/-- Parameter zero is exactly the vanishing locus of the coordinate section. -/
theorem parameterZeroInclusion_range :
    Set.range QuotientFiber.BundleCycles.parameterZeroInclusion.{u} =
      (Deformation.Parameter.BundleCycles.deformationParameterLine.basicOpen parameterLineSection : Set Deformation.Parameter.BundleCycles.deformationParameterLine)ᶜ := by
  let A : CommRingCat := .of (Polynomial (ULift.{u} ℤ))
  let B : CommRingCat := .of (Polynomial (ULift.{u} ℤ) ⧸ QuotientFiber.BundleCycles.parameterZeroIdeal)
  let g : A ⟶ B := CommRingCat.ofHom (Ideal.Quotient.mk QuotientFiber.BundleCycles.parameterZeroIdeal)
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g.hom = QuotientFiber.BundleCycles.parameterZeroIdeal := Ideal.mk_ker
  change Set.range (PrimeSpectrum.comap g.hom) = _
  rw [range_comap_of_surjective _ _ hsurj, hker]
  change PrimeSpectrum.zeroLocus QuotientFiber.BundleCycles.parameterZeroIdeal =
    ((Spec A).basicOpen ((Scheme.ΓSpecIso A).inv Polynomial.X) : Set (Spec A))ᶜ
  rw [basicOpen_eq_of_affine]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  change Ideal.span {Polynomial.X} ≤ x.asIdeal ↔ ¬Polynomial.X ∉ x.asIdeal
  exact (Ideal.span_singleton_le_iff_mem (I := x.asIdeal)).trans not_not.symm

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual global regular parameter section. -/
def globalDeformationParameterSection : Γ(Deformation.BundleCycles.globalDeformation I, ⊤) :=
  (Deformation.Parameter.BundleCycles.globalDeformationParameter I).appTop parameterLineSection

/-- Restricting the global section gives the original affine Laurent parameter. -/
theorem globalDeformationParameterSection_on_chart (U : X.AffineZariskiSite) :
    ((Deformation.BundleCycles.globalDeformationCover I).f U).appTop (globalDeformationParameterSection I) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U) := by
  let a : CommRingCat.of (Polynomial (ULift.{u} ℤ)) ⟶
      CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) :=
    CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap (I.ideal U))
  have h := congrArg (fun k => k.appTop parameterLineSection)
    (Deformation.Parameter.BundleCycles.globalDeformationParameter_on_chart I U)
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) Polynomial.X
  change (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))).inv
      (Deformation.Parameter.BundleCycles.deformationParameterRingMap (I.ideal U) Polynomial.X) =
    (Spec.map a).appTop parameterLineSection at he
  rw [Deformation.Parameter.BundleCycles.deformationParameterRingMap_X] at he
  exact h.trans he.symm

/-- The global closed-fiber embedding has exactly the vanishing locus of t as its range. -/
theorem globalSpecialFiberMap_range :
    Set.range (SpecialFiber.BundleCycles.globalSpecialFiberMap I) =
      ((Deformation.BundleCycles.globalDeformation I).basicOpen (globalDeformationParameterSection I) :
        Set (Deformation.BundleCycles.globalDeformation I))ᶜ := by
  have h := Scheme.image_preimage_eq_of_isPullback (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback I).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  change Set.range (SpecialFiber.BundleCycles.globalSpecialFiberMap I) =
    Deformation.Parameter.BundleCycles.globalDeformationParameter I ⁻¹' Set.range QuotientFiber.BundleCycles.parameterZeroInclusion at h
  rw [parameterZeroInclusion_range, Set.preimage_compl] at h
  have hb := Scheme.preimage_basicOpen_top (Deformation.Parameter.BundleCycles.globalDeformationParameter I) parameterLineSection
  exact h.trans (congrArg (fun U : (Deformation.BundleCycles.globalDeformation I).Opens => (U : Set (Deformation.BundleCycles.globalDeformation I))ᶜ) hb)

/-- The canonical affine normal-cone chart as a morphism into the global cone. -/
def globalNormalConeChartMap (U : X.AffineZariskiSite) :
    Normal.Cone.BundleCycles.affineNormalCone (I.ideal U) ⟶ SpecialFiber.BundleCycles.globalSpecialFiber I :=
  (SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ (SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U

theorem globalNormalConeChartMap_toDeformation (U : X.AffineZariskiSite) :
    globalNormalConeChartMap I U ≫ SpecialFiber.BundleCycles.globalSpecialFiberMap I =
      Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) ≫ (Deformation.BundleCycles.globalDeformationCover I).f U := by
  let a : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) ⟶
      CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))
  let b : CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)) ⟶
      CommRingCat.of (Normal.Cone.BundleCycles.NormalConeRing (I.ideal U)) :=
    CommRingCat.ofHom (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U)).symm.toRingHom
  have h : (SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ Spec.map a =
      Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) := (Spec.map_comp a b).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ k)
      (SpecialFiber.BundleCycles.globalSpecialFiberMap_on_chart I U)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (Deformation.BundleCycles.globalDeformationCover I).f U) h)))

variable [IsIntegral X]

/-- The global parameter is nonzero, as can be checked on any nonempty affine chart. -/
theorem globalDeformationParameterSection_ne_zero : globalDeformationParameterSection I ≠ 0 := by
  let x : X := Classical.choice inferInstance
  let U : X.AffineZariskiSite := (directedCover X).idx x
  obtain ⟨y, _⟩ := (directedCover X).covers x
  have : Nonempty U.1 := ⟨y⟩
  have : IsDomain Γ(X, U.1) := inferInstance
  intro hz
  have h := congrArg ((Deformation.BundleCycles.globalDeformationCover I).f U).appTop hz
  rw [globalDeformationParameterSection_on_chart I U] at h
  exact Affine.Specialization.BundleCycles.affineDeformationParameterSection_ne_zero (I.ideal U)
    (h.trans (map_zero ((Deformation.BundleCycles.globalDeformationCover I).f U).appTop.hom))

variable [AlgebraicGeometry.IsNoetherian X]

/-- The finite effective divisor of t on the actual global deformation. -/
def globalDeformationParameterDivisor : Deformation.BundleCycles.globalDeformation I →₀ ℤ :=
  RegularDivisor.BundleCycles.regularFunctionDivisor (Deformation.BundleCycles.globalDeformation I) (globalDeformationParameterSection I)

theorem globalDeformationParameterDivisor_nonnegative (x : Deformation.BundleCycles.globalDeformation I) :
    0 ≤ globalDeformationParameterDivisor I x :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_nonnegative _ _ (globalDeformationParameterSection_ne_zero I) x

theorem globalDeformationParameterDivisor_support :
    ((globalDeformationParameterDivisor I).support : Set (Deformation.BundleCycles.globalDeformation I)) ⊆
      Set.range (SpecialFiber.BundleCycles.globalSpecialFiberMap I) := by
  rw [globalSpecialFiberMap_range]
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset _ _

/-- The point embedding of the globally glued normal cone. -/
def globalSpecialFiberPointEmbedding : SpecialFiber.BundleCycles.globalSpecialFiber I ↪ Deformation.BundleCycles.globalDeformation I :=
  ⟨SpecialFiber.BundleCycles.globalSpecialFiberMap I, (SpecialFiber.BundleCycles.globalSpecialFiberMap I).isClosedEmbedding.injective⟩

/-- The entire parameter divisor, transported to the actual global normal cone. -/
def globalSpecializationCycle : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  Finsupp.comapDomain (globalSpecialFiberPointEmbedding I) (globalDeformationParameterDivisor I)
    (globalSpecialFiberPointEmbedding I).injective.injOn

@[simp]
theorem globalSpecializationCycle_apply (x : SpecialFiber.BundleCycles.globalSpecialFiber I) :
    globalSpecializationCycle I x = globalDeformationParameterDivisor I (SpecialFiber.BundleCycles.globalSpecialFiberMap I x) := rfl

/-- Pushing the specialization cycle back recovers every coefficient of the divisor of t. -/
theorem globalSpecializationCycle_push :
    Finsupp.embDomain (globalSpecialFiberPointEmbedding I) (globalSpecializationCycle I) =
      globalDeformationParameterDivisor I :=
  Finsupp.embDomain_comapDomain (globalDeformationParameterDivisor_support I)

theorem globalSpecializationCycle_nonnegative (x : SpecialFiber.BundleCycles.globalSpecialFiber I) :
    0 ≤ globalSpecializationCycle I x := globalDeformationParameterDivisor_nonnegative I _

/-- The global multiplicity is the actual length of the local quotient by t. -/
theorem globalSpecializationCycle_coeff_length (x : SpecialFiber.BundleCycles.globalSpecialFiber I)
    (hx : coheight (SpecialFiber.BundleCycles.globalSpecialFiberMap I x) = 1) :
    globalSpecializationCycle I x =
      ((Module.length ((Deformation.BundleCycles.globalDeformation I).presheaf.stalk (SpecialFiber.BundleCycles.globalSpecialFiberMap I x))
        (((Deformation.BundleCycles.globalDeformation I).presheaf.stalk (SpecialFiber.BundleCycles.globalSpecialFiberMap I x)) ⧸
          Ideal.span {(Deformation.BundleCycles.globalDeformation I).presheaf.germ ⊤ (SpecialFiber.BundleCycles.globalSpecialFiberMap I x)
            (by trivial) (globalDeformationParameterSection I)})).toNat : ℤ) :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ (globalDeformationParameterSection_ne_zero I) _ hx

/-- The global parameter divisor restricts to the affine divisor with the same local lengths. -/
theorem globalDeformationParameterDivisor_on_chart (U : X.AffineZariskiSite) [Nonempty U.1]
    (x : (Deformation.BundleCycles.globalDeformationCover I).X U) :
    globalDeformationParameterDivisor I ((Deformation.BundleCycles.globalDeformationCover I).f U x) =
      Affine.Specialization.BundleCycles.affineDeformationParameterDivisor (I.ideal U) x := by
  have : IsDomain Γ(X, U.1) := inferInstance
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsIntegral ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
    inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))))
  have : AlgebraicGeometry.IsNoetherian ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian
      (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))))
  have h := DivisorRestriction.BundleCycles.regularFunctionDivisor_openImmersion ((Deformation.BundleCycles.globalDeformationCover I).f U)
    (globalDeformationParameterSection I) (globalDeformationParameterSection_ne_zero I) x
  rw [globalDeformationParameterSection_on_chart I U] at h
  exact h.symm

/-- The global specialization agrees with every actual affine normal-cone specialization. -/
theorem globalSpecializationCycle_on_chart (U : X.AffineZariskiSite) [Nonempty U.1]
    (x : Normal.Cone.BundleCycles.affineNormalCone (I.ideal U)) :
    globalSpecializationCycle I (globalNormalConeChartMap I U x) =
      Affine.Specialization.BundleCycles.affineSpecializationCycle (I.ideal U) x := by
  have : IsDomain Γ(X, U.1) := inferInstance
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have h := congrArg (fun k => k x) (globalNormalConeChartMap_toDeformation I U)
  change SpecialFiber.BundleCycles.globalSpecialFiberMap I (globalNormalConeChartMap I U x) =
    (Deformation.BundleCycles.globalDeformationCover I).f U (Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) x) at h
  rw [globalSpecializationCycle_apply, h]
  exact globalDeformationParameterDivisor_on_chart I U (Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization.BundleCycles
