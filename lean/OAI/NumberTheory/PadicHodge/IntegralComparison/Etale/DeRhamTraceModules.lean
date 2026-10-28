import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent
import OAI.NumberTheory.PadicHodge.IntegralComparison.AdjunctionSectionLift

/-! # De Rham Trace Modules -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceModules

noncomputable section

/-! The coordinate-independent trace gives actual morphisms of the native
differential-form module sheaves on affine étale charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower (MvPolynomial σ R) A B]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Fintype σ] [LinearOrder σ]
  {ι : Type v} [Fintype ι] (b : Module.Basis ι A B)

theorem formTrace_smul (n : ℕ) (a : A) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :
    DeRhamTraceCoordinates.formTrace R A B σ b n (a • ω) = a • DeRhamTraceCoordinates.formTrace R A B σ b n ω := by
  let e := (FormScalarExtension.isBaseChange R A B σ n).equiv
  obtain ⟨z, rfl⟩ := e.surjective ω
  induction z using TensorProduct.inductionOn with
  | tmul x η =>
    change DeRhamTraceCoordinates.formTrace R A B σ b n
      (a • (x • OrdinaryFormScalars.Ordinary.map R A B n η)) =
        a • DeRhamTraceCoordinates.formTrace R A B σ b n (x • OrdinaryFormScalars.Ordinary.map R A B n η)
    rw [← smul_assoc, DeRhamTraceCoordinates.trace_projection_formula, DeRhamTraceCoordinates.trace_projection_formula,
      (Algebra.trace A B).map_smul, smul_assoc]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

def formTraceLinear (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n →ₗ[A]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n where
  toFun := DeRhamTraceCoordinates.formTrace R A B σ b n
  map_add' := (DeRhamTraceCoordinates.formTrace R A B σ b n).map_add
  map_smul' := formTrace_smul R A B σ b n

def formTraceModule (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)) ⟶
      ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)))
    (Y := ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)) {
    toFun := fun ω => DeRhamTraceCoordinates.formTrace R A B σ b n ω
    map_add' := (DeRhamTraceCoordinates.formTrace R A B σ b n).map_add
    map_smul' := fun a ω => by
      change DeRhamTraceCoordinates.formTrace R A B σ b n ((algebraMap A B a) • ω) = _
      exact (congrArg (DeRhamTraceCoordinates.formTrace R A B σ b n)
        (IsScalarTower.algebraMap_smul B a (show AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n from ω))).trans
          (formTrace_smul R A B σ b n a ω) }

def affineMapOfSections (M N : (Spec (CommRingCat.of A)).Modules)
    [M.IsQuasicoherent]
    (t : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj M ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of A)).obj N) : M ⟶ N := by
  let : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of A) M
  let : IsIso ((tilde.adjunction (R := CommRingCat.of A)).counit.app M) :=
    show IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) M) from inferInstance
  let : IsIso (tilde.adjunction (R := CommRingCat.of A)).unit :=
    show IsIso (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom from inferInstance
  exact AdjunctionSectionLift.lift (tilde.adjunction (R := CommRingCat.of A)) M N t

theorem affineMapOfSections_sections (M N : (Spec (CommRingCat.of A)).Modules)
    [M.IsQuasicoherent]
    (t : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj M ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of A)).obj N) :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map (affineMapOfSections A M N t) = t := by
  let : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of A) M
  let : IsIso ((tilde.adjunction (R := CommRingCat.of A)).counit.app M) :=
    show IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) M) from inferInstance
  let : IsIso (tilde.adjunction (R := CommRingCat.of A)).unit :=
    show IsIso (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom from inferInstance
  exact AdjunctionSectionLift.map_lift (tilde.adjunction (R := CommRingCat.of A)) M N t

abbrev affineFormSheaf (n : ℕ) : (Spec (CommRingCat.of A)).Modules :=
  AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R A) n

def affineFormSectionsIso (n : ℕ) :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (affineFormSheaf R A n) ≅
      ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  Affine.LocalizingModule.globalIso A
    (AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R A)) n)
    (fun a => AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.restriction R A σ a n) ≪≫
    (LinearEquiv.ofBijective (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormSections.BaseAffineOrdinaryFormSections.map R A ⊤ n).hom
      (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormSections.BaseAffineOrdinaryFormSections.top_bijective R A n)).toModuleIso.symm

def affinePushforwardFormSectionsIso (n : ℕ) :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (affineFormSheaf R B n)) ≅
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)) :=
  (AlgebraicGeometry.Picard.PoincareBundle.TildePullback.pushforwardSectionsIso (CommRingCat.ofHom (algebraMap A B))).app
      (affineFormSheaf R B n) ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapIso (affineFormSectionsIso R B σ n)

/-- The trace on the original module sheaves, with the genuine geometric
direct image as its source. -/
def affineSheafTrace (n : ℕ) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (affineFormSheaf R B n) ⟶ affineFormSheaf R A n := by
  let F := affineFormSheaf R B n
  let G := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F
  let : F.IsQuasicoherent := AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.quasicoherent R B σ n
  let : G.IsQuasicoherent := AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent.pushforward_isQuasicoherent
    (CommRingCat.ofHom (algebraMap A B)) F
  exact affineMapOfSections A G (affineFormSheaf R A n)
    ((affinePushforwardFormSectionsIso R A B σ n).hom ≫ formTraceModule R A B σ b n ≫
      (affineFormSectionsIso R A σ n).inv)

theorem affineSheafTrace_sections (n : ℕ) :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map (affineSheafTrace R A B σ b n) =
      (affinePushforwardFormSectionsIso R A B σ n).hom ≫ formTraceModule R A B σ b n ≫
        (affineFormSectionsIso R A σ n).inv := by
  let : (affineFormSheaf R B n).IsQuasicoherent :=
    AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.quasicoherent R B σ n
  let : ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (affineFormSheaf R B n)).IsQuasicoherent :=
    AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent.pushforward_isQuasicoherent
      (CommRingCat.ofHom (algebraMap A B)) (affineFormSheaf R B n)
  unfold affineSheafTrace
  exact affineMapOfSections_sections A _ _ _

variable (τ : Type u) [Fintype τ] [LinearOrder τ]
  [Algebra (MvPolynomial τ R) A] [Algebra (MvPolynomial τ R) B]
  [IsScalarTower R (MvPolynomial τ R) A] [IsScalarTower R (MvPolynomial τ R) B]
  [IsScalarTower (MvPolynomial τ R) A B]
  [Algebra.FormallyEtale (MvPolynomial τ R) A]
  [Algebra.FormallyEtale (MvPolynomial τ R) B]
  {κ : Type w} [Fintype κ] (c : Module.Basis κ A B)

theorem affineSheafTrace_coordinate_independent (n : ℕ) :
    affineSheafTrace R A B σ b n = affineSheafTrace R A B τ c n := by
  have ht : formTraceModule R A B σ b n = formTraceModule R A B τ c n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact congrArg (fun t => t.f n ω) (DeRhamTraceCoordinates.trace_coordinate_independent R A B σ b τ c)
  unfold affineSheafTrace
  rw [ht]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceModules
