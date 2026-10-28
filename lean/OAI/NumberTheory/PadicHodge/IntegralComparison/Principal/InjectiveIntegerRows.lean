import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedRows

/-! # Injective Integer Rows -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows

/-! The actual shifted injective terms give exact supported Cech rows
for principal diagrams preserving nonempty intersections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison
variable {X : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  (G : C ⥤ X.Opens) {ι : Type} [LinearOrder ι] (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G]
  (N : X.Modules) (c : ℕ)

theorem exactAt_succ (q r : ℕ) :
    ((Supported.OrderedCechEdge.bicomplex ℤ X G W
      (InjectiveIntegerCoordinates.complex N c)).X q).ExactAt (r+1) := by
  let : TopCat.Sheaf.IsFlasque
      ((ShiftedOpenInjectiveResolution.complex (AffinePrincipal.Injective.Comparison.sheaf N) c).X q) :=
    ShiftedOpenInjectiveResolution.term_flasque (AffinePrincipal.Injective.Comparison.sheaf N) c q
  let : TopCat.Sheaf.IsFlasque
      ((InjectiveIntegerCoordinates.complex N c).X q) :=
    Additive.IntegerSheaf.flasque X _
  exact FlasqueOrderedRows.exactAt_succ ℤ X G W
    ((InjectiveIntegerCoordinates.complex N c).X q) r

end NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows

namespace NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows.SingleSupportedCandidate

/-! The selected-support extension on the original single quasicoherent
coefficient Cech complex. The intervening injective resolution is the
actual chosen resolution, and both restriction and fixedness transfer
through the checked affine Cech comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugate_section {D : Type*} [Category D]
    {A B C E : D} (e : A ≅ C) (f : B ≅ E)
    (s : B ⟶ A) (r : A ⟶ B) (t : C ⟶ E)
    (hs : s ≫ r = 𝟙 B) (ht : e.hom ≫ t = r ≫ f.hom) :
    (f.inv ≫ s ≫ e.hom) ≫ t = 𝟙 E := by
  simp only [Category.assoc]
  rw [ht, ← Category.assoc s r, hs, Category.id_comp, f.inv_hom_id]

private theorem conjugate_natural {D : Type*} [Category D]
    {A B C E A' B' C' E' : D}
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C') (eE : E ≅ E')
    (a : A ⟶ B) (b : C ⟶ E) (c : A ⟶ C) (d : B ⟶ E)
    (a' : A' ⟶ B') (b' : C' ⟶ E')
    (ha : eA.hom ≫ a' = a ≫ eB.hom)
    (hb : eC.hom ≫ b' = b ≫ eE.hom) (h : a ≫ d = c ≫ b) :
    a' ≫ (eB.inv ≫ d ≫ eE.hom) = (eA.inv ≫ c ≫ eC.hom) ≫ b' := by
  apply (cancel_epi eA.hom).mp
  simp only [Category.assoc]
  rw [← Category.assoc eA.hom a', ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hb, ← Category.assoc a d, ← Category.assoc c b, h]

variable {X : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  (G₁ G₂ : C ⥤ X.Opens) {ι : Type} [LinearOrder ι] (W : ι → C) (O₁ O₂ : X.Opens)

/-- The geometric cover conditions for the original and selected supports.
All row exactness is derived from the chosen injective resolution. -/
structure Conditions : Prop where
  outside_le : O₁ ≤ O₂
  intersection_eq : G₂.obj (⊤_ C) ⊓ O₁ = G₂.obj (⊤_ C) ⊓ O₂
  local_global : G₂.obj (⊤_ C) ⊔ O₂ = ⊤
  wide_global : G₁.obj (⊤_ C) ⊔ O₁ = ⊤
  wide_punctured : ∀ i, G₁.obj (W i) ≤ O₁
  local_punctured : ∀ i, G₂.obj (W i) ≤ O₁
  wide_cover : G₁.obj (⊤_ C) ⊓ O₁ ≤ ⨆ i, G₁.obj (W i)
  local_cover : G₂.obj (⊤_ C) ⊓ O₁ ≤ ⨆ i, G₂.obj (W i)
  wide_affine : ∀ r, IsAffineOpen (G₁.obj r)
  local_affine : ∀ r, IsAffineOpen (G₂.obj r)

namespace Conditions
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
variable {G₁ G₂ W O₁ O₂} (H : Conditions G₁ G₂ W O₁ O₂)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G₁]
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G₂]
  (N : X.Modules) (c : ℕ)

def moduleCandidate (q : ℕ) : (InjectiveIntegerCoordinates.total G₂ W N c).homology q ⟶ (InjectiveIntegerCoordinates.total G₁ W N c).homology q :=
  Supported.CechLocalizedExtension.candidate ℤ X G₁ G₂ W O₁ O₂ H.outside_le
    H.intersection_eq H.local_global (InjectiveIntegerCoordinates.complex N c) H.wide_punctured H.local_punctured
    H.wide_cover H.local_cover
    (exactAt_succ G₁ W N c)
    (exactAt_succ G₂ W N c) q

def moduleForget (q : ℕ) : (InjectiveIntegerCoordinates.total G₁ W N c).homology q ⟶ (InjectiveIntegerCoordinates.globalComplex N c).homology q :=
  Supported.OrderedCech.Comparison.forgetSupport ℤ X G₁ W O₁ (InjectiveIntegerCoordinates.complex N c)
    H.wide_punctured H.wide_cover (exactAt_succ G₁ W N c)
    H.wide_global q

def moduleSelectedExtension (q : ℕ) :
    (InjectiveIntegerCoordinates.total G₂ W N c).homology q ⟶ (InjectiveIntegerCoordinates.globalComplex N c).homology q :=
  (Supported.OrderedCech.Comparison.homologyIso ℤ X G₂ W O₁ (InjectiveIntegerCoordinates.complex N c)
    H.local_punctured H.local_cover (exactAt_succ G₂ W N c) q).inv ≫
      homologyMap (Supported.CechLocalizedExtension.globalSectionCandidate ℤ X G₂ O₁ O₂
        H.intersection_eq H.local_global (InjectiveIntegerCoordinates.complex N c)) q

theorem module_global (q : ℕ) : H.moduleCandidate N c q ≫ H.moduleForget N c q =
    H.moduleSelectedExtension N c q :=
  Supported.CechLocalizedExtension.candidate_global ℤ X G₁ G₂ W O₁ O₂ H.outside_le
    H.intersection_eq H.local_global (InjectiveIntegerCoordinates.complex N c) H.wide_punctured H.local_punctured
    H.wide_cover H.local_cover
    (exactAt_succ G₁ W N c)
    (exactAt_succ G₂ W N c) H.wide_global q

variable [N.IsQuasicoherent]

def candidate (q : ℕ) :
    (AffinePrincipal.Injective.Comparison.source G₂ W N c).homology q ⟶
      (AffinePrincipal.Injective.Comparison.source G₁ W N c).homology q :=
  (InjectiveIntegerCoordinates.bridge G₂ W N c H.local_affine q).inv ≫ InjectiveIntegerCoordinates.forget.map (H.moduleCandidate N c q) ≫
    (InjectiveIntegerCoordinates.bridge G₁ W N c H.wide_affine q).hom

def forgetSupport (q : ℕ) :
    (AffinePrincipal.Injective.Comparison.source G₁ W N c).homology q ⟶
      (InjectiveIntegerCoordinates.additiveGlobalComplex N c).homology q :=
  (InjectiveIntegerCoordinates.bridge G₁ W N c H.wide_affine q).inv ≫ InjectiveIntegerCoordinates.forget.map (H.moduleForget N c q) ≫ (InjectiveIntegerCoordinates.globalIso N c q).hom

def selectedExtension (q : ℕ) :
    (AffinePrincipal.Injective.Comparison.source G₂ W N c).homology q ⟶
      (InjectiveIntegerCoordinates.additiveGlobalComplex N c).homology q :=
  (InjectiveIntegerCoordinates.bridge G₂ W N c H.local_affine q).inv ≫ InjectiveIntegerCoordinates.forget.map (H.moduleSelectedExtension N c q) ≫
    (InjectiveIntegerCoordinates.globalIso N c q).hom

theorem candidate_restriction (α : G₂ ⟶ G₁) (q : ℕ) :
    H.candidate N c q ≫
      homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap G₁ G₂ α W N c) q = 𝟙 _ := by
  apply conjugate_section (InjectiveIntegerCoordinates.bridge G₁ W N c H.wide_affine q) (InjectiveIntegerCoordinates.bridge G₂ W N c H.local_affine q)
    (InjectiveIntegerCoordinates.forget.map (H.moduleCandidate N c q))
    (InjectiveIntegerCoordinates.forget.map (homologyMap (InjectiveIntegerCoordinates.restriction G₁ W N c G₂ α) q))
  · rw [← CategoryTheory.Functor.map_comp]
    have hs := Supported.CechLocalizedExtension.candidate_restriction ℤ X G₁ G₂ α W O₁ O₂
      H.outside_le H.intersection_eq H.local_global (InjectiveIntegerCoordinates.complex N c) H.wide_punctured H.local_punctured
      H.wide_cover H.local_cover
      (exactAt_succ G₁ W N c)
      (exactAt_succ G₂ W N c) q
    exact (congrArg InjectiveIntegerCoordinates.forget.map hs).trans (CategoryTheory.Functor.map_id _ _)
  · exact (InjectiveIntegerCoordinates.bridge_restriction G₁ W N c G₂ α H.wide_affine H.local_affine q).symm

theorem candidate_global (q : ℕ) : H.candidate N c q ≫ H.forgetSupport N c q =
    H.selectedExtension N c q := by
  have h := congrArg InjectiveIntegerCoordinates.forget.map (H.module_global N c q)
  rw [CategoryTheory.Functor.map_comp] at h
  dsimp only [Conditions.candidate, Conditions.forgetSupport, Conditions.selectedExtension]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun a => (InjectiveIntegerCoordinates.bridge G₂ W N c H.local_affine q).inv ≫ a ≫ (InjectiveIntegerCoordinates.globalIso N c q).hom) h

variable {P : X.Modules} [P.IsQuasicoherent] (f : N ⟶ P)

theorem candidate_natural (q : ℕ) :
    homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G₂ W N c f) q ≫ H.candidate P c q =
      H.candidate N c q ≫ homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G₁ W N c f) q := by
  apply conjugate_natural
    (InjectiveIntegerCoordinates.bridge G₂ W N c H.local_affine q) (InjectiveIntegerCoordinates.bridge G₂ W P c H.local_affine q)
    (InjectiveIntegerCoordinates.bridge G₁ W N c H.wide_affine q) (InjectiveIntegerCoordinates.bridge G₁ W P c H.wide_affine q)
    (InjectiveIntegerCoordinates.forget.map (homologyMap (InjectiveIntegerCoordinates.totalMap G₂ W N c f) q))
    (InjectiveIntegerCoordinates.forget.map (homologyMap (InjectiveIntegerCoordinates.totalMap G₁ W N c f) q))
    (InjectiveIntegerCoordinates.forget.map (H.moduleCandidate N c q)) (InjectiveIntegerCoordinates.forget.map (H.moduleCandidate P c q))
  · exact (InjectiveIntegerCoordinates.bridge_naturality G₂ W N c f H.local_affine q).symm
  · exact (InjectiveIntegerCoordinates.bridge_naturality G₁ W N c f H.wide_affine q).symm
  · rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg InjectiveIntegerCoordinates.forget.map
    exact Supported.CechLocalizedExtension.candidate_natural ℤ X G₁ G₂ W O₁ O₂ H.outside_le
      H.intersection_eq H.local_global (InjectiveIntegerCoordinates.complex N c) H.wide_punctured H.local_punctured
      H.wide_cover H.local_cover
      (exactAt_succ G₁ W N c)
      (exactAt_succ G₂ W N c) (InjectiveIntegerCoordinates.complexMap N c f)
      (exactAt_succ G₁ W P c)
      (exactAt_succ G₂ W P c) q

theorem candidate_fixed (a : N ⟶ N) (q : ℕ)
    (x : (AffinePrincipal.Injective.Comparison.source G₂ W N c).homology q)
    (hx : homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G₂ W N c a) q x = x) :
    homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G₁ W N c a) q (H.candidate N c q x) =
      H.candidate N c q x := by
  have hn := ConcreteCategory.congr_hom (H.candidate_natural N c a q) x
  change H.candidate N c q (homologyMap
    (AffinePrincipal.Injective.Comparison.sourceMap G₂ W N c a) q x) = _ at hn
  rw [hx] at hn
  exact hn.symm

end Conditions

end NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows.SingleSupportedCandidate

end

end OAI
