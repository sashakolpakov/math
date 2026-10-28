import OAI.AlgebraicGeometry.Resolution.Blowups.Open.IdealSheafBaseChange

/-! # Open Ideal Sheaf Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafGluing.Construction

noncomputable section

/-! Gluing finitely many compatible ideal sheaves on quasi-compact open subschemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} [Finite ι]
  (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X)
  [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
  (J : ∀ i, (U i).IdealSheafData)

/-- The global ideal sheaf obtained by intersecting the finitely many
extensions of the local ideals. -/
def gluedFiniteOpenIdealSheaf : X.IdealSheafData := ⨅ i, (J i).map (j i)

/-- Compatibility on the actual pairwise pullbacks proves that the
constructed global ideal restricts exactly to each prescribed local ideal. -/
theorem gluedFiniteOpenIdealSheaf_restrict
    (hcompat : ∀ a b : ι,
      (J a).comap (pullback.fst (j a) (j b)) =
        (J b).comap (pullback.snd (j a) (j b))) (a : ι) :
    (gluedFiniteOpenIdealSheaf U j J).comap (j a) = J a := by
  apply le_antisymm
  · exact (Scheme.IdealSheafData.comap_mono (j a) (iInf_le _ a)).trans
      (Scheme.IdealSheafData.comap_map_le (J a) (j a))
  · unfold gluedFiniteOpenIdealSheaf
    rw [Open.IdealSheafBaseChange.Construction.idealSheaf_open_comap_iInf]
    apply le_iInf
    intro b
    rw [Open.IdealSheafBaseChange.Construction.idealSheaf_open_comap_map, ← hcompat a b]
    exact Scheme.IdealSheafData.le_map_comap (J a) (pullback.fst (j a) (j b))

/-- Compatible finite local data give an actual global ideal sheaf,
with exact agreement on every specified open. -/
theorem exists_idealSheaf_of_finite_open_compatibility
    (hcompat : ∀ a b : ι,
      (J a).comap (pullback.fst (j a) (j b)) =
        (J b).comap (pullback.snd (j a) (j b))) :
    ∃ I : X.IdealSheafData, ∀ a, I.comap (j a) = J a :=
  ⟨gluedFiniteOpenIdealSheaf U j J, gluedFiniteOpenIdealSheaf_restrict U j J hcompat⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafGluing.Construction
