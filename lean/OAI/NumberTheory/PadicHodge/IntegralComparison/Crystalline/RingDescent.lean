import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.AmbientContinuous

/-! # Ring Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RingDescent

noncomputable section

/-!
# IntegralComparison: ambient rings already satisfy crystalline descent

Global sections are a ring-valued sheaf on the big Zariski site. The
continuous ambient functor and the canonical global-sections isomorphism
identify its restriction with the actual ambient-ring presheaf.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

def specCoyonedaIso (R : CommRingCat.{u}) : yoneda.obj (Spec R) ≅
    (Scheme.Spec.rightOp.op ⋙ coyoneda).obj (op R) :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun g => g.op
      invFun := fun g => g.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)

lemma gamma_isSheaf : Presheaf.IsSheaf Scheme.zariskiTopology Scheme.Γ := by
  intro R
  apply Presieve.isSheaf_iso Scheme.zariskiTopology
    ((ΓSpec.adjunction.rightOp.compCoyonedaIso).app (op R))
  exact Presieve.isSheaf_iso Scheme.zariskiTopology (specCoyonedaIso R)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.zariskiTopology) (yoneda.obj (Spec R)))

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

def ringPresheaf : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := U.unop.ring
  map α := CommRingCat.ofHom α.unop.ringMap.toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def gammaIso : (BigCrystallineSite.Object.ambient (p := p) (J := J) (δ := δ) (f := f)).op ⋙ Scheme.Γ ≅ ringPresheaf f :=
  NatIso.ofComponents (fun U => Scheme.ΓSpecIso U.unop.ring) (fun α =>
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom α.unop.ringMap.toRingHom))

lemma ringPresheaf_isSheaf : Presheaf.IsSheaf BigCrystallineSite.Object.topology (ringPresheaf (p := p) (J := J) (δ := δ) f) :=
  (Presheaf.isSheaf_of_iso_iff (gammaIso f)).mp
    ((BigCrystallineSite.Object.ambient (p := p) (J := J) (δ := δ) (f := f)).op_comp_isSheaf_of_isSheaf
      BigCrystallineSite.Object.topology Scheme.zariskiTopology Scheme.Γ gamma_isSheaf)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RingDescent
