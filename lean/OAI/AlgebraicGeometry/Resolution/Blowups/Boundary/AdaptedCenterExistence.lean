import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterExtension

/-! # Adapted Center Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterExistence.Construction

noncomputable section

/-! Simultaneous preservation of every boundary equation inside an actual framed center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

/-- At every point of a framed center containing a finite dual boundary
family, an actual affine open chart has a center frame containing all of
those exact boundary equations as distinct generators. -/
theorem exists_boundary_adapted_center_open_chart (n : ℕ) :
    ∀ (R : CommRingCat.{u}) [Algebra k R] {ι : Type u} [Fintype ι] [DecidableEq ι]
      (g : ι → R) (D : ι → Derivation k R R)
      (_hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
      (w : Fin n → R) (E : Fin n → Derivation k R R)
      (_hE : ∀ i j, E i (w j) = if i = j then 1 else 0)
      (_hw : ∀ i, w i ∈ Ideal.span (Set.range g))
      (p : PrimeSpectrum R) (_hgp : Ideal.span (Set.range g) ≤ p.asIdeal),
      Nonempty (AdaptedCenterChart.Construction.BoundaryAdaptedCenterOpenChart k R (Ideal.span (Set.range g)) w p) := by
  induction n with
  | zero =>
      intro R _ ι _ _ g D hD w E hE hw p hgp
      refine ⟨{ carrier := R
                algebra := inferInstance
                map := AlgHom.id k R
                isOpenImmersion := by
                  change IsOpenImmersion (Spec.map (𝟙 R))
                  rw [Spec.map_id]
                  infer_instance
                point := p
                point_over := ?_
                indices := ι
                finite := inferInstance
                decidableEq := inferInstance
                generators := g
                derivations := D
                dual := hD
                centerSpan := ?_
                boundaryIndex := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
                boundaryCoordinates := fun i => Fin.elim0 i }⟩
      · apply PrimeSpectrum.ext
        rfl
      · simp
  | succ n ih =>
      intro R _ ι _ _ g D hD w E hE hw p hgp
      have hEtail : ∀ i j : Fin n, E i.succ (w j.succ) = if i = j then 1 else 0 := by
        intro i j
        simpa only [Fin.succ_inj] using hE i.succ j.succ
      obtain ⟨C⟩ := ih R g D hD (fun j => w j.succ) (fun j => E j.succ) hEtail
        (fun j => hw j.succ) p hgp
      exact AdaptedCenterExtension.Construction.extend_boundary_adapted_center_chart k R _ w p hgp (E 0)
        (by simpa using hE 0 0)
        (fun j => by simpa only [ite_eq_right (Ne.symm (Fin.succ_ne_zero j))] using hE 0 j.succ) (hw 0) C

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterExistence.Construction
