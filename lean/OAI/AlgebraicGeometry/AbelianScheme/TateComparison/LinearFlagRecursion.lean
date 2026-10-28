import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

/-! # Linear Flag Recursion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagRecursion.LinearBlockFlags

noncomputable section

/-! Ordinary chosen lattice flags decompose into their first lattice
choice and a flag beginning at that lattice. -/

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
  {s : ℕ} (π : R) (L₀ : Fin s → Duality.RankThreeLattice R K)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.NextChoices (t : Local.IntegralType s) := ∀ v : Fin s,
  {M : Duality.RankThreeLattice R K // Duality.RelativePosition π (t.val.exponent v) (L₀ v) M}

variable {π L₀} {t : Local.IntegralType s} {ts : List (Local.IntegralType s)}

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.nil : Duality.LinearBlockFlags π L₀ [] :=
  ⟨fun _ => L₀, rfl, fun j => Fin.elim0 j⟩

instance : Subsingleton (Duality.LinearBlockFlags π L₀ []) := ⟨fun F G => by
  apply Subtype.ext
  funext j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  exact F.property.1.trans G.property.1.symm⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.first (F : Duality.LinearBlockFlags π L₀ (t :: ts)) : Duality.LinearBlockFlags.NextChoices π L₀ t :=
  fun v => ⟨F.val (Fin.succ 0) v, by
    have h := F.property.2 0 v
    change Duality.RelativePosition π (t.val.exponent v) (F.val 0 v) (F.val (Fin.succ 0) v) at h
    rw [F.property.1] at h
    exact h⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.tail (F : Duality.LinearBlockFlags π L₀ (t :: ts)) :
    Duality.LinearBlockFlags π (fun v => (Duality.LinearBlockFlags.first F v).val) ts :=
  ⟨fun j => F.val j.succ, rfl, fun j v => F.property.2 j.succ v⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.cons (M : Duality.LinearBlockFlags.NextChoices π L₀ t)
    (F : Duality.LinearBlockFlags π (fun v => (M v).val) ts) : Duality.LinearBlockFlags π L₀ (t :: ts) := by
  refine ⟨Fin.cases L₀ F.val, rfl, ?_⟩
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro v
    change Duality.RelativePosition π (t.val.exponent v) (L₀ v) (F.val 0 v)
    rw [F.property.1]
    exact (M v).property
  · exact F.property.2 i

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.cons_first_tail (F : Duality.LinearBlockFlags π L₀ (t :: ts)) : Duality.LinearBlockFlags.cons (Duality.LinearBlockFlags.first F) (Duality.LinearBlockFlags.tail F) = F := by
  apply Subtype.ext
  funext j
  refine Fin.cases F.property.1.symm (fun _ => rfl) j

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.first_cons (M : Duality.LinearBlockFlags.NextChoices π L₀ t)
    (F : Duality.LinearBlockFlags π (fun v => (M v).val) ts) : Duality.LinearBlockFlags.first (Duality.LinearBlockFlags.cons M F) = M := by
  funext v
  apply Subtype.ext
  exact congrFun F.property.1 v

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality.LinearBlockFlags.consEquiv : Duality.LinearBlockFlags π L₀ (t :: ts) ≃
    Σ M : Duality.LinearBlockFlags.NextChoices π L₀ t, Duality.LinearBlockFlags π (fun v => (M v).val) ts where
  toFun F := ⟨Duality.LinearBlockFlags.first F, Duality.LinearBlockFlags.tail F⟩
  invFun G := Duality.LinearBlockFlags.cons G.1 G.2
  left_inv := Duality.LinearBlockFlags.cons_first_tail
  right_inv G := by
    rcases G with ⟨M, F⟩
    apply Sigma.ext (Duality.LinearBlockFlags.first_cons M F)
    apply (Subtype.heq_iff_coe_eq (fun l => iff_of_eq
      (congrArg (fun N : Duality.LinearBlockFlags.NextChoices π L₀ t =>
        Duality.IsChosenBlockFlag π (fun v => (N v).val) ts l) (Duality.LinearBlockFlags.first_cons M F)))).mpr
    rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagRecursion.LinearBlockFlags
