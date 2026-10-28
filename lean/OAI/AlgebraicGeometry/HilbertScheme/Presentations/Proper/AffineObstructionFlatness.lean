import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ClosedFiberFlatness

/-! # Affine Obstruction Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineObstructionFlatness

noncomputable section

/-! A proper family over a Noetherian local base is flat if each affine
chart has flat reduction and zero ideal-tensor obstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v
variable (A : CommRingCat.{u}) [IsLocalRing A] [IsNoetherianRing A]
variable {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]
variable (C : X.AffineCover.{v} (@IsOpenImmersion))
variable [∀ i, Algebra A (C.X i)] [∀ i, IsNoetherianRing (C.X i)]

theorem proper_flat_of_affine_idealTensor_injective
    (hC : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (C.X i))) = C.f i ≫ f)
    (I : Ideal A) (hI : I ≠ ⊤)
    [∀ i, Module.Flat (A ⧸ I) ((C.X i) ⧸ I.map (algebraMap A (C.X i)))]
    (hinj : ∀ i, Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A (C.X i) I)) :
    Flat f := by
  apply ClosedFiberFlatness.proper_flat_of_closedFiberStalks A f
  intro x hx
  obtain ⟨i, p, hp⟩ := C.cover.exists_eq x
  change C.I₀ at i
  change Spec (C.X i) at p
  change C.f i p = x at hp
  subst x
  have hcp : Spec.map (CommRingCat.ofHom (algebraMap A (C.X i))) p =
      IsLocalRing.closedPoint A := by
    rw [hC i, Scheme.Hom.comp_apply]
    exact hx
  have ht := Affine.ClosedFiberFlatness.affine_closedFiber_stalk_flat A (C.X i) p hcp I hI (hinj i)
  let g := C.f i
  let : IsOpenImmersion g := C.map_prop i
  have : MorphismProperty.RespectsIso @Flat.{u} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ a (_ : IsIso a) => inferInstanceAs (Flat a))
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @Flat)
    (Spec.map (g.stalkMap p)) ((X.fromSpecStalk (g p)) ≫ f)).mp
  rw [← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  simpa only [g, ← hC i] using ht

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineObstructionFlatness
