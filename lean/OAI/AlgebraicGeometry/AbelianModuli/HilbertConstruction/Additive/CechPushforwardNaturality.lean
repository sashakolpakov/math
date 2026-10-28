import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CechPushforward

/-! # Cech Pushforward Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CechPushforwardNaturality

noncomputable section

/-! The inverse-image-cover comparison is natural for every map of additive presheaves, including the native Cech open-factor restrictions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {X P : Scheme.{u}} (a : P ⟶ X)
variable {F G : P.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (e : F ⟶ G)
variable {ι : Type u} (U : ι → X.Opens)

theorem additiveCechPushforwardFactorIso_naturality (n : ℕ) (i : Fin (n + 1) → ι) :
    e.app (op (∏ᶜ fun k => a ⁻¹ᵁ U (i k))) ≫ (CechPushforward.additiveCechPushforwardFactorIso a G U n i).hom =
      (CechPushforward.additiveCechPushforwardFactorIso a F U n i).hom ≫
        e.app (op (a ⁻¹ᵁ (∏ᶜ fun k => U (i k)))) :=
  (e.naturality (eqToIso (CoefficientCech.PushforwardFactors.preimageCechIntersection a U n i)).op.hom).symm

theorem additiveCechPushforwardComplexIso_naturality :
    (cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).map e ≫
        (CechPushforward.additiveCechPushforwardComplexIso a G U).hom =
      (CechPushforward.additiveCechPushforwardComplexIso a F U).hom ≫
        (cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change CategoryTheory.Limits.Pi.map (fun i : Fin (n + 1) → ι => e.app (op (∏ᶜ fun k => a ⁻¹ᵁ U (i k)))) ≫
      CategoryTheory.Limits.Pi.map (fun i : Fin (n + 1) → ι => (CechPushforward.additiveCechPushforwardFactorIso a G U n i).hom) =
    CategoryTheory.Limits.Pi.map (fun i : Fin (n + 1) → ι => (CechPushforward.additiveCechPushforwardFactorIso a F U n i).hom) ≫
      CategoryTheory.Limits.Pi.map (fun i : Fin (n + 1) → ι => e.app (op (a ⁻¹ᵁ (∏ᶜ fun k => U (i k)))))
  rw [CategoryTheory.Limits.Pi.map_comp_map, CategoryTheory.Limits.Pi.map_comp_map]
  apply congrArg CategoryTheory.Limits.Pi.map
  funext i
  exact additiveCechPushforwardFactorIso_naturality a e U n i

theorem additiveCechPushforwardComplexIso_inv_naturality :
    (cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e) ≫
        (CechPushforward.additiveCechPushforwardComplexIso a G U).inv =
      (CechPushforward.additiveCechPushforwardComplexIso a F U).inv ≫
        (cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).map e := by
  apply (cancel_epi (CechPushforward.additiveCechPushforwardComplexIso a F U).hom).mp
  rw [← Category.assoc, ← additiveCechPushforwardComplexIso_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CechPushforwardNaturality
