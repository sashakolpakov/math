import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointCoordinateProjectiveAction

/-! # Projective Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport

noncomputable section

/-! An orbit relation between framed configurations determines
one actual projective coordinate isomorphism. Its independence of
linear representatives gives the cocycle needed for descent. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type v}

def ConfigurationFrameRelated (v w : ι → Fin (n + 1) → R) : Prop :=
  ∃ T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R), ∃ s : ι → Rˣ,
    ∀ z, w z = (s z : R) • T (v z)

def configurationProjectiveTransport (v w : ι → Fin (n + 1) → R) (h : ConfigurationFrameRelated v w) :
    Projective.ProjectivePresentations.affineProjectiveSpace R n ≅ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  PointCoordinateProjectiveAction.pointCoordinateProjectiveIso h.choose

theorem configurationProjectiveTransport_eq_of_choice
    (v w : ι → Fin (n + 1) → R) (h : ConfigurationFrameRelated v w)
    (σ : Fin (n + 1) → ι) (b : ι)
    (hframe : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => v (σ k)) (v b)))
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)
    (hs : ∀ z, w z = (s z : R) • T (v z)) :
    (configurationProjectiveTransport v w h).hom = (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom := by
  let U := h.choose
  let t := h.choose_spec.choose
  have ht : ∀ z, w z = (t z : R) • U (v z) := h.choose_spec.choose_spec
  apply PointCoordinateProjectiveAction.pointCoordinateProjectiveIso_frame_unique v σ b hframe U T (fun z => (t z)⁻¹ * s z)
  intro z
  calc
    U (v z) = (t z)⁻¹ • ((t z) • U (v z)) := (inv_smul_smul (t z) (U (v z))).symm
    _ = (t z)⁻¹ • w z := congrArg (fun x => (t z)⁻¹ • x) (ht z).symm
    _ = ((t z)⁻¹ * s z) • T (v z) := by
      rw [hs, mul_smul]
      rfl

theorem configurationProjectiveTransport_cocycle
    (v w z : ι → Fin (n + 1) → R)
    (hvw : ConfigurationFrameRelated v w) (hwz : ConfigurationFrameRelated w z) (hvz : ConfigurationFrameRelated v z)
    (σv σw : Fin (n + 1) → ι) (bv bw : ι)
    (hv : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => v (σv k)) (v bv)))
    (hw : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => w (σw k)) (w bw))) :
    (configurationProjectiveTransport v w hvw).hom ≫ (configurationProjectiveTransport w z hwz).hom =
      (configurationProjectiveTransport v z hvz).hom := by
  obtain ⟨T, s, hs⟩ := hvw
  obtain ⟨U, t, ht⟩ := hwz
  have hcomp : ∀ a, z a = (t a * s a : Rˣ) • (T.trans U) (v a) := by
    intro a
    rw [ht, hs, U.map_smul, mul_smul]
    rfl
  have h₁ := configurationProjectiveTransport_eq_of_choice v w ⟨T, s, hs⟩ σv bv hv T s hs
  have h₂ := configurationProjectiveTransport_eq_of_choice w z ⟨U, t, ht⟩ σw bw hw U t ht
  have h₃ := configurationProjectiveTransport_eq_of_choice v z hvz σv bv hv
    (T.trans U) (fun a => t a * s a) hcomp
  exact (congrArg₂ (fun a b : Projective.ProjectivePresentations.affineProjectiveSpace R n ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n => a ≫ b)
    h₁ h₂).trans ((PointCoordinateProjectiveAction.pointCoordinateProjectiveIso_trans T U).symm.trans h₃.symm)

theorem configurationProjectiveTransport_self
    (v : ι → Fin (n + 1) → R) (h : ConfigurationFrameRelated v v)
    (σ : Fin (n + 1) → ι) (b : ι)
    (hv : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => v (σ k)) (v b))) :
    (configurationProjectiveTransport v v h).hom = 𝟙 _ := by
  rw [configurationProjectiveTransport_eq_of_choice v v h σ b hv (LinearEquiv.refl R _) (fun _ => 1)
    (fun _ => by simp)]
  exact PointCoordinateProjectiveAction.pointCoordinateProjectiveIso_refl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport
