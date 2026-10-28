import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ClosedFiberFlatness
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Closed Fiber Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ClosedFiberFlatness

noncomputable section

/-! The residue obstruction criterion at actual stalks of an affine chart
whose point lies above the closed point of a Noetherian local base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u
variable (A S : CommRingCat.{u}) [IsLocalRing A] [IsNoetherianRing A]
variable [Algebra A S] [IsNoetherianRing S]

theorem affine_closedFiber_stalk_flat (p : PrimeSpectrum S)
    (hp : Spec.map (CommRingCat.ofHom (algebraMap A S)) p = IsLocalRing.closedPoint A)
    (I : Ideal A) (hI : I ≠ ⊤)
    [Module.Flat (A ⧸ I) (S ⧸ I.map (algebraMap A S))]
    (hinj : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A S I)) :
    Flat ((Spec S).fromSpecStalk p ≫ Spec.map (CommRingCat.ofHom (algebraMap A S))) := by
  let q : Spec S := p
  let T : Type u := (Spec S).presheaf.stalk q
  let : IsLocalRing T := inferInstanceAs (IsLocalRing ((Spec S).presheaf.stalk q))
  let : Algebra S T := (StructureSheaf.toStalk S p).hom.toAlgebra
  let : IsLocalization.AtPrime T p.asIdeal := StructureSheaf.IsLocalization.to_stalk S p
  let : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
  let : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have he : Spec.map (CommRingCat.ofHom (algebraMap A T)) =
      (Spec S).fromSpecStalk p ≫ Spec.map (CommRingCat.ofHom (algebraMap A S)) := by
    erw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp]
    rfl
  have : IsLocalHom (algebraMap A T) := by
    apply (IsLocalRing.isLocalHom_iff_comap_closedPoint _).mpr
    change Spec.map (CommRingCat.ofHom (algebraMap A T)) (IsLocalRing.closedPoint T) = _
    rw [he]
    erw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
    exact hp
  have : IsNoetherianRing T := IsLocalization.isNoetherianRing p.asIdeal.primeCompl T inferInstance
  have : Module.Flat A T := Localized.QuotientFlatness.localized_flat_of_idealTensor_injective A S T
    p.asIdeal.primeCompl I hI hinj
  rw [← he, Flat.SpecMap_iff]
  exact inferInstanceAs (Module.Flat A T)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ClosedFiberFlatness
