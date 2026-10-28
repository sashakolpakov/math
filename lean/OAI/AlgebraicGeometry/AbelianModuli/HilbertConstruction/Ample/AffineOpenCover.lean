import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteFlatCoverDescent

/-! # Affine Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over an affine base, ampleness on a proper scheme can be checked after an arbitrary affine open cover of the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem Line.Bundles.LineBundle.isAmple_of_affine_open_cover
    {S X : Scheme.{u}} [IsAffine S] (p : X ⟶ S) [IsProper p]
    (C : Scheme.OpenCover.{v} S) [∀ i, IsAffine (C.X i)]
    (L : Line.Bundles.LineBundle X) (hL : ∀ i, (L.pullback (pullback.fst p (C.f i))).IsAmple) : L.IsAmple := by
  let D := C.finiteSubcover
  let : Fintype D.I₀ := Fintype.ofFinite D.I₀
  have : Small.{u} D.I₀ := small_map (Fintype.equivFin D.I₀)
  have (i : D.I₀) : IsAffine (D.X i) := by
    change IsAffine (C.X _)
    infer_instance
  apply L.isAmple_of_finite_affine_flat_cover D.X p D.f
  · intro s
    obtain ⟨x, hx⟩ := D.covers s
    exact ⟨D.idx s, x, hx⟩
  · intro i
    exact hL _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
