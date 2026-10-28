import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

/-! # Action Base Change Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison

noncomputable section

section

/-! Actual integral actions transport bijectively through group-scheme
isomorphisms by conjugating every coefficient endomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    {R : Type} [CommRing R]

local instance (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : IsMonHom e.symm.hom :=
  inferInstanceAs (IsMonHom e.inv)

def transportIntegralAction (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B :=
  Finite.Actions.integralActionOfRingHom B ((Finite.Actions.GroupEndRing.transport e).comp (Finite.Actions.ringHomOfIntegralAction A ρ))

theorem transportIntegralAction_map (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (r : R) :
    (transportIntegralAction e ρ).map r = e.inv ≫ ρ.map r ≫ e.hom := rfl

theorem transportIntegralAction_inverse (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) :
    transportIntegralAction e.symm (transportIntegralAction e ρ) = ρ := by
  apply Finite.Actions.integralAction_ext
  intro r
  simp only [transportIntegralAction_map, Iso.symm_inv, Iso.symm_hom,
    Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def integralActionTransportEquiv (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A ≃ AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B where
  toFun := transportIntegralAction e
  invFun := transportIntegralAction e.symm
  left_inv := transportIntegralAction_inverse e
  right_inv := transportIntegralAction_inverse e.symm

end

/-! The actual family comparison for changing the base of the action
functor, with its compatibility with maps of test schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ActionBaseChange
variable {S B : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : B ⟶ S)

def groupIso (T : Over B) : ((A.pullback b).pullback T.hom).scheme ≅
    (A.pullback ((Over.map b).obj T).hom).scheme := (A.pullbackCompIso b T.hom).symm

instance (T : Over B) : IsMonHom (groupIso A b T).hom := by
  dsimp [groupIso]
  infer_instance

def schemeIso (T : Over B) : ((A.pullback b).pullback T.hom).scheme.left ≅
    (A.pullback ((Over.map b).obj T).hom).scheme.left :=
  (Over.forget T.left).mapIso (groupIso A b T)

@[reassoc]
theorem schemeIso_hom_fst (T : Over B) : (schemeIso A b T).hom ≫
    pullback.fst A.scheme.hom (T.hom ≫ b) =
      pullback.fst (A.pullback b).scheme.hom T.hom ≫ pullback.fst A.scheme.hom b :=
  A.pullbackCompIso_inv_left_fst b T.hom

@[reassoc]
theorem schemeIso_inv_fst_fst (T : Over B) : (schemeIso A b T).inv ≫
    pullback.fst (A.pullback b).scheme.hom T.hom ≫ pullback.fst A.scheme.hom b =
      pullback.fst A.scheme.hom (T.hom ≫ b) := by
  rw [← schemeIso_hom_fst, Iso.inv_hom_id_assoc]

theorem familyMap_comparison {T U : Over B} (f : T ⟶ U) :
    EndomorphismFamiliesId.EndomorphismFamilies.familyMap A ((Over.map b).map f) ≫ (schemeIso A b U).inv =
      (schemeIso A b T).inv ≫ EndomorphismFamiliesId.EndomorphismFamilies.familyMap (A.pullback b) f := by
  apply (cancel_mono (schemeIso A b U).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [EndomorphismFamiliesId.EndomorphismFamilies.familyMap_fst]
    change pullback.fst A.scheme.hom (T.hom ≫ b) =
      ((schemeIso A b T).inv ≫ EndomorphismFamiliesId.EndomorphismFamilies.familyMap (A.pullback b) f ≫ (schemeIso A b U).hom) ≫
        pullback.fst A.scheme.hom (U.hom ≫ b)
    simp only [Category.assoc, schemeIso_hom_fst, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_fst_assoc, schemeIso_inv_fst_fst]
  · have hu : (schemeIso A b U).hom ≫ pullback.snd A.scheme.hom (U.hom ≫ b) =
        pullback.snd (A.pullback b).scheme.hom U.hom := (groupIso A b U).hom.w
    have ht : (schemeIso A b T).inv ≫ pullback.snd (A.pullback b).scheme.hom T.hom =
        pullback.snd A.scheme.hom (T.hom ≫ b) := (groupIso A b T).inv.w
    rw [EndomorphismFamiliesId.EndomorphismFamilies.familyMap_snd]
    change pullback.snd A.scheme.hom (T.hom ≫ b) ≫ f.left =
      ((schemeIso A b T).inv ≫ EndomorphismFamiliesId.EndomorphismFamilies.familyMap (A.pullback b) f ≫ (schemeIso A b U).hom) ≫
        pullback.snd A.scheme.hom (U.hom ≫ b)
    simp only [Category.assoc, hu, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_snd, reassoc_of% ht]

end ActionBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison
