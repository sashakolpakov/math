import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalDomainConnected
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralIdempotents
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalIdempotentExt

/-! # Clopen Idempotents -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenIdempotents.Construction

noncomputable section

/-!
# Completion: actual global idempotents for open-and-closed decompositions

The characteristic function of an open-and-closed subscheme is constructed
in its actual global section ring by the sheaf product decomposition.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The complementary open subscheme of an open-and-closed subscheme. -/
def clopenComplement {X : Scheme.{u}} (U : X.Opens) (hU : IsClosed (U : Set X)) : X.Opens :=
  ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩

/-- The actual global section ring decomposes over complementary open subschemes. -/
def clopenGlobalFunctionProductIso {X : Scheme.{u}} (U : X.Opens) (hU : IsClosed (U : Set X)) :
    Γ(X, ⊤) ≅ CommRingCat.of (Γ(X, U) × Γ(X, clopenComplement U hU)) := by
  have hu : U ⊔ clopenComplement U hU = ⊤ := by ext; simp [clopenComplement]
  have hd : U ⊓ clopenComplement U hU = ⊥ := by ext; simp [clopenComplement]
  exact X.presheaf.mapIso (eqToIso hu).op ≪≫
    (X.sheaf.isProductOfDisjoint U (clopenComplement U hU) hd).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit Γ(X, U) Γ(X, clopenComplement U hU))

/-- The first coordinate is restriction to the original open subscheme. -/
theorem clopenGlobalFunctionProductIso_fst {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    (clopenGlobalFunctionProductIso U hU).hom ≫
      CommRingCat.ofHom (RingHom.fst Γ(X, U) Γ(X, clopenComplement U hU)) =
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  have hd : U ⊓ clopenComplement U hU = ⊥ := by ext; simp [clopenComplement]
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (X.sheaf.isProductOfDisjoint U (clopenComplement U hU) hd)
    (CommRingCat.prodFanIsLimit Γ(X, U) Γ(X, clopenComplement U hU)) ⟨WalkingPair.left⟩
  simp only [CommRingCat.prodFan, BinaryFan.π_app_left, BinaryFan.mk_fst] at h
  dsimp [clopenGlobalFunctionProductIso]
  rw [Category.assoc, h]
  change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _
  rw [← Functor.map_comp]
  congr 1

/-- The second coordinate is restriction to the complementary open subscheme. -/
theorem clopenGlobalFunctionProductIso_snd {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    (clopenGlobalFunctionProductIso U hU).hom ≫
      CommRingCat.ofHom (RingHom.snd Γ(X, U) Γ(X, clopenComplement U hU)) =
        X.presheaf.map (homOfLE (show clopenComplement U hU ≤ ⊤ from le_top)).op := by
  have hd : U ⊓ clopenComplement U hU = ⊥ := by ext; simp [clopenComplement]
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (X.sheaf.isProductOfDisjoint U (clopenComplement U hU) hd)
    (CommRingCat.prodFanIsLimit Γ(X, U) Γ(X, clopenComplement U hU)) ⟨WalkingPair.right⟩
  simp only [CommRingCat.prodFan, BinaryFan.π_app_right, BinaryFan.mk_snd] at h
  dsimp [clopenGlobalFunctionProductIso]
  rw [Category.assoc, h]
  change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _
  rw [← Functor.map_comp]
  congr 1

/-- The actual global function equal to one on the clopen piece and zero on its complement. -/
def clopenIndicator {X : Scheme.{u}} (U : X.Opens) (hU : IsClosed (U : Set X)) : Γ(X, ⊤) :=
  (clopenGlobalFunctionProductIso U hU).inv (1, 0)

theorem clopenIndicator_isIdempotent {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsIdempotentElem (clopenIndicator U hU) := by
  have h : IsIdempotentElem ((1, 0) : Γ(X, U) × Γ(X, clopenComplement U hU)) := by
    change (1, 0) * (1, 0) = (1, 0)
    simp
  exact h.map (clopenGlobalFunctionProductIso U hU).inv.hom

/-- Restriction of the actual indicator to its clopen piece is one. -/
theorem clopenIndicator_restrict {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (clopenIndicator U hU) = 1 := by
  rw [← clopenGlobalFunctionProductIso_fst U hU]
  simp [clopenIndicator]

/-- Restriction of the actual indicator to its complement is zero. -/
theorem clopenIndicator_restrict_complement {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    X.presheaf.map (homOfLE (show clopenComplement U hU ≤ ⊤ from le_top)).op
      (clopenIndicator U hU) = 0 := by
  rw [← clopenGlobalFunctionProductIso_snd U hU]
  simp [clopenIndicator]

/-- The nonzero locus of the actual idempotent is precisely the prescribed clopen piece. -/
theorem clopenIndicator_basicOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : X.basicOpen (clopenIndicator U hU) = U := by
  have h₁ := congrArg (fun s : Γ(X, U) => X.basicOpen s) (clopenIndicator_restrict U hU)
  have h₀ := congrArg (fun s : Γ(X, clopenComplement U hU) => X.basicOpen s)
    (clopenIndicator_restrict_complement U hU)
  simp only [Scheme.basicOpen_res, Scheme.basicOpen_one] at h₁
  simp only [Scheme.basicOpen_res, Scheme.basicOpen_zero] at h₀
  apply le_antisymm
  · intro x hx
    by_contra hn
    have hx' : x ∈ clopenComplement U hU ⊓ X.basicOpen (clopenIndicator U hU) := ⟨hn, hx⟩
    rw [h₀] at hx'
    exact hx'
  · exact inf_eq_left.mp h₁

/-- Pullback carries the actual indicator to the indicator of the inverse-image clopen piece. -/
theorem clopenIndicator_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsClosed (U : Set Y)) :
    f.appTop (clopenIndicator U hU) =
      clopenIndicator (f ⁻¹ᵁ U) (hU.preimage f.continuous) := by
  apply GlobalIdempotentExt.Construction.global_idempotent_ext ((clopenIndicator_isIdempotent U hU).map f.appTop.hom)
    (clopenIndicator_isIdempotent _ _)
  rw [← Scheme.preimage_basicOpen_top, clopenIndicator_basicOpen, clopenIndicator_basicOpen]

/-- The actual indicator is zero exactly when its clopen piece is empty. -/
theorem clopenIndicator_eq_zero_iff {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : clopenIndicator U hU = 0 ↔ U = ⊥ := by
  constructor
  · intro h
    rw [← clopenIndicator_basicOpen U hU, h, Scheme.basicOpen_zero]
  · intro h
    apply GlobalIdempotentExt.Construction.global_idempotent_ext (clopenIndicator_isIdempotent U hU) (by simp [IsIdempotentElem])
    simp [clopenIndicator_basicOpen, h]

/-- The actual indicator is one exactly when its clopen piece is the whole scheme. -/
theorem clopenIndicator_eq_one_iff {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : clopenIndicator U hU = 1 ↔ U = ⊤ := by
  constructor
  · intro h
    rw [← clopenIndicator_basicOpen U hU, h, Scheme.basicOpen_one]
  · intro h
    apply GlobalIdempotentExt.Construction.global_idempotent_ext (clopenIndicator_isIdempotent U hU) (by simp [IsIdempotentElem])
    simp [clopenIndicator_basicOpen, h]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenIdempotents.Construction
