import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine Coefficient Objects -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoefficientObjects.Abelian

noncomputable section

/-!
Actual affine objects of finite presentation descend to finite coefficient
rings over an arbitrary ground ring. In particular the ground ring may
be the rationals and the ambient coefficient field the complex numbers.
This is the object step needed before spreading a whole abelian variety.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

def affineCoefficientObject (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

def affineCoefficientBaseChangeIso (R B A : Type)
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A] :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
      (affineCoefficientObject R A) ≅ affineCoefficientObject B (B ⊗[R] A) :=
  Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R B A) (by
    change (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R B A).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R] A))) = _
    rw [pullbackSpecIso_hom_fst, pullbackSymmetry_hom_comp_fst]
    rfl)

def affineCoefficientAlgIso {B A A' : Type} [CommRing B] [CommRing A] [CommRing A']
    [Algebra B A] [Algebra B A'] (e : A ≃ₐ[B] A') :
    affineCoefficientObject B A ≅ affineCoefficientObject B A' :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op) (by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B A')) =
        Spec.map (CommRingCat.ofHom (algebraMap B A))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact e.symm.commutes x)

structure CoefficientSchemeModel (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (X : Over (Spec (CommRingCat.of B))) where
  coefficients : Finset B
  model : Over (Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B coefficients)))
  finitePresentation : LocallyOfFinitePresentation model.hom
  quasiCompact : QuasiCompact model.hom
  quasiSeparated : QuasiSeparated model.hom
  comparison : (Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B coefficients) B)))).obj model ≅ X

attribute [instance] CoefficientSchemeModel.finitePresentation CoefficientSchemeModel.quasiCompact
  CoefficientSchemeModel.quasiSeparated

theorem affine_object_has_coefficient_model (R B A : Type)
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra B A]
    [Algebra.FinitePresentation B A] :
    Nonempty (CoefficientSchemeModel R B (affineCoefficientObject B A)) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation B A
  let s : Finset B := P.finite_coeffs.toFinset
  let L := FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s
  let : P.HasCoeffs L := ⟨fun c hc =>
    ⟨⟨c, Algebra.subset_adjoin (by simpa [s] using hc)⟩, rfl⟩⟩
  let A₀ := P.ModelOfHasCoeffs L
  refine ⟨{
    coefficients := s
    model := affineCoefficientObject L A₀
    finitePresentation := ?_
    quasiCompact := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap L A₀))))
    quasiSeparated := inferInstanceAs (QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap L A₀))))
    comparison := affineCoefficientBaseChangeIso L B A₀ ≪≫
      affineCoefficientAlgIso (P.tensorModelOfHasCoeffsEquiv L) }⟩
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

def CoefficientSchemeModel.transport {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {X Y : Over (Spec (CommRingCat.of B))} (M : CoefficientSchemeModel R B X) (e : X ≅ Y) :
    CoefficientSchemeModel R B Y :=
  { M with comparison := M.comparison ≪≫ e }

theorem isAffine_object_has_coefficient_model (R B : Type)
    [CommRing R] [CommRing B] [Algebra R B]
    (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left] [LocallyOfFinitePresentation X.hom] :
    Nonempty (CoefficientSchemeModel R B X) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra B A := φ.hom.toAlgebra
  have hφFP : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  let : Algebra.FinitePresentation B A := (LocallyOfFinitePresentation.SpecMap_iff φ).mp hφFP
  obtain ⟨M⟩ := affine_object_has_coefficient_model R B A
  let e : X ≅ affineCoefficientObject B A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  exact ⟨M.transport e.symm⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoefficientObjects.Abelian
