import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.FilteredNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.Row

/-! # Boundary Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.BoundaryLifting

noncomputable section

/-! Lifting total boundaries back to boundaries in the augmented complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- A final-row inclusion has every earlier row zero. -/
theorem final_row_inclusion_zero_before (n : ℕ) (x : (K.X n).X 0) :
    CycleNormalization.ZeroRowsBefore K n (K.ιTotal (.up ℕ) n 0 n rfl x) n := by
  intro a b hab ha
  have hn : n ≠ a := by omega
  change (K.ιTotal (.up ℕ) n 0 n rfl ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K a b n) x = 0
  simp [hn]

/-- A preimage can be normalized to its final row while preserving its differential. -/
theorem exists_final_row_preimage (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (himage : CycleNormalization.ZeroRowsBefore K (n + 1) ((K.total (.up ℕ)).d n (n + 1) x) n)
    (hrows : CycleNormalization.RowsExact K) :
    ∃ y : (K.total (.up ℕ)).X n, CycleNormalization.ZeroRowsBefore K n y n ∧
      (K.total (.up ℕ)).d n (n + 1) y = (K.total (.up ℕ)).d n (n + 1) x := by
  cases n with
  | zero =>
      refine ⟨x, ?_, rfl⟩
      intro a b hab ha
      omega
  | succ n =>
      obtain ⟨z, hz⟩ := FilteredNormalization.exists_normalize_from_image K n x himage hrows
      exact ⟨x - (K.total (.up ℕ)).d n (n + 1) z, hz, FilteredNormalization.total_sub_boundary_d K n x z⟩

/-- If the edge image of an element is a total boundary, that element was already
a boundary in the augmented complex. -/
theorem exists_horizontal_boundary_lift
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : CycleNormalization.RowsExact K)
    (n : ℕ) (a : A.X (n + 1)) (z : (K.total (.up ℕ)).X n)
    (hza : (K.total (.up ℕ)).d n (n + 1) z =
      (HorizontalEdge.totalUpNatHorizontalEdge K A e he w).f (n + 1) a) :
    ∃ b : A.X n, A.d n (n + 1) b = a := by
  have himage : CycleNormalization.ZeroRowsBefore K (n + 1)
      ((K.total (.up ℕ)).d n (n + 1) z) (n + 1) := by
    rw [hza]
    exact final_row_inclusion_zero_before K (n + 1) (e (n + 1) a)
  obtain ⟨z', hz', hd'⟩ := exists_final_row_preimage K n z
    (FilteredNormalization.zeroRowsBefore_mono K himage (Nat.le_succ n)) hrows
  have hcomponent : FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 1 (n + 1)
      ((K.total (.up ℕ)).d n (n + 1) z') = 0 := by
    rw [hd']
    exact himage n 1 rfl (Nat.lt_succ_self n)
  have hrow := FilteredNormalization.row_cycle_of_output_coordinate_zero K n n 0 rfl z' hz' hcomponent
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp (haug n) _ hrow
  refine ⟨b, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (e (n + 1))).mp (hmono (n + 1))
  have heval := ConcreteCategory.congr_hom (he n (n + 1) rfl) b
  have hfinal : FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (n + 1) 0 (n + 1)
      ((HorizontalEdge.totalUpNatHorizontalEdge K A e he w).f (n + 1) a) = e (n + 1) a := by
    change (K.ιTotal (.up ℕ) (n + 1) 0 (n + 1) rfl ≫
      FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (n + 1) 0 (n + 1)) (e (n + 1) a) = e (n + 1) a
    simp
  have hdcoord := congrArg (fun f => f z') (BoundaryCoordinates.total_d_π_zero_right K n)
  change FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (n + 1) 0 (n + 1)
      ((K.total (.up ℕ)).d n (n + 1) z') =
    (K.d n (n + 1)).f 0 (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n z') at hdcoord
  rw [hd', hza, hfinal, ← hb] at hdcoord
  exact heval.symm.trans hdcoord.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.BoundaryLifting
