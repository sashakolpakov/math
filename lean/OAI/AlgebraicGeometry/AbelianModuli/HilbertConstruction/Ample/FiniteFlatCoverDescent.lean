import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.BaseFamilyAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FlatAffineDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Finite Flat Cover Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness on a proper scheme over an affine base descends from a finite covering family of flat affine schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem Line.Bundles.LineBundle.isAmple_of_finite_affine_flat_cover
    {S X : Scheme.{u}} [IsAffine S] {ι : Type v} [Finite ι] [Small.{u} ι]
    (Y : ι → Scheme.{u}) [∀ i, IsAffine (Y i)] (p : X ⟶ S) [IsProper p]
    (f : ∀ i, Y i ⟶ S) [∀ i, Flat (f i)]
    (hcover : ∀ s : S, ∃ i, ∃ y : Y i, f i y = s)
    (L : Line.Bundles.LineBundle X) (hL : ∀ i, (L.pullback (pullback.fst p (f i))).IsAmple) : L.IsAmple := by
  have : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  let g := Sigma.desc f
  have : Flat g := IsZariskiLocalAtSource.sigmaDesc (fun i => inferInstanceAs (Flat (f i)))
  have : Surjective g := ⟨fun s => by
    obtain ⟨i, y, hy⟩ := hcover s
    exact ⟨Sigma.ι Y i y,
      (congrArg (fun r : Y i ⟶ S => r y) (Sigma.ι_comp_desc f i)).trans hy⟩⟩
  exact L.isAmple_of_flat_affine_baseChange p g (L.isAmple_baseChange_sigma Y p f hL)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
