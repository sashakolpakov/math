import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagRecursion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ChosenLatticeNeighbors

/-! # Linear Flag Endpoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagEndpoints

noncomputable section

/-! Enumerating ordinary lattice flags retains every intermediate
lattice choice and hence gives the ordinary neighbor multiplicities. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

theorem mem_chosenLatticeNeighbors_iff (t : Local.IntegralType s) (L M : ChosenLatticeNeighbors.ChosenLatticePoint s q) :
    M ∈ ChosenLatticeNeighbors.chosenLatticeNeighbors s q t L ↔
      ∀ v, Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v) (L v) (M v) := by
  rw [← Multiset.count_pos, ChosenLatticeNeighbors.chosenLatticeNeighbors_count]
  split_ifs <;> simp_all

theorem chosenLatticeNeighbors_nodup (t : Local.IntegralType s) (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) :
    (ChosenLatticeNeighbors.chosenLatticeNeighbors s q t L).Nodup := by
  apply Multiset.nodup_iff_count_le_one.mpr
  intro M
  rw [ChosenLatticeNeighbors.chosenLatticeNeighbors_count]
  split_ifs <;> omega

def nextChoiceLattices {L : ChosenLatticeNeighbors.ChosenLatticePoint s q} {t : Local.IntegralType s}
    (M : Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t) : ChosenLatticeNeighbors.ChosenLatticePoint s q :=
  fun v => (M v).val

theorem nextChoiceLattices_injective {L : ChosenLatticeNeighbors.ChosenLatticePoint s q} {t : Local.IntegralType s} :
    Function.Injective (nextChoiceLattices s q (L := L) (t := t)) := by
  intro M N h
  funext v
  exact Subtype.ext (congrFun h v)

instance finiteNextChoices (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (t : Local.IntegralType s) :
    Finite (Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t) := by
  let f : Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t →
      ↥(ChosenLatticeNeighbors.chosenLatticeNeighbors s q t L).toFinset := fun M =>
    ⟨nextChoiceLattices s q M, Multiset.mem_toFinset.mpr
      ((mem_chosenLatticeNeighbors_iff s q t L _).mpr (fun v => (M v).property))⟩
  exact Finite.of_injective f (fun _ _ h => nextChoiceLattices_injective s q (congrArg Subtype.val h))

theorem nextChoices_enumeration (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (t : Local.IntegralType s) :
    let : Fintype (Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t) := Fintype.ofFinite _
    (Finset.univ : Finset (Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t)).val.map
      (nextChoiceLattices s q) = ChosenLatticeNeighbors.chosenLatticeNeighbors s q t L := by
  let : Fintype (Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t) := Fintype.ofFinite _
  apply (Multiset.Nodup.ext
    (Finset.univ.nodup.map (nextChoiceLattices_injective s q))
    (chosenLatticeNeighbors_nodup s q t L)).mpr
  intro M
  rw [Multiset.mem_map, mem_chosenLatticeNeighbors_iff]
  constructor
  · rintro ⟨N, _, rfl⟩ v
    exact (N v).property
  · intro h
    exact ⟨fun v => ⟨M v, h v⟩, Finset.mem_univ _, rfl⟩

instance finiteLinearBlockFlags (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (ts : List (Local.IntegralType s)) :
    Finite (Duality.LinearBlockFlags (q : ℤ_[q]) L ts) := by
  induction ts generalizing L with
  | nil => infer_instance
  | cons t ts ih =>
    have : ∀ M : Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t,
        Finite (Duality.LinearBlockFlags (q : ℤ_[q]) (nextChoiceLattices s q M) ts) := fun M => ih _
    exact Finite.of_equiv _ Duality.LinearBlockFlags.consEquiv.symm

def linearFlagEndpoints (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (ts : List (Local.IntegralType s)) :
    Multiset (ChosenLatticeNeighbors.ChosenLatticePoint s q) :=
  let : Fintype (Duality.LinearBlockFlags (q : ℤ_[q]) L ts) := Fintype.ofFinite _
  (Finset.univ : Finset (Duality.LinearBlockFlags (q : ℤ_[q]) L ts)).val.map
    (fun F => F.val (Fin.last ts.length))

theorem linearFlagEndpoints_nil (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) : linearFlagEndpoints s q L [] = {L} := by
  let : Fintype (Duality.LinearBlockFlags (q : ℤ_[q]) L []) := Fintype.ofFinite _
  have hu : (Finset.univ : Finset (Duality.LinearBlockFlags (q : ℤ_[q]) L [])) =
      {Duality.LinearBlockFlags.nil (π := (q : ℤ_[q])) (L₀ := L)} := by
    ext F
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  change (Finset.univ : Finset (Duality.LinearBlockFlags (q : ℤ_[q]) L [])).val.map _ = _
  rw [hu]
  rfl

theorem linearFlagEndpoints_cons (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (t : Local.IntegralType s)
    (ts : List (Local.IntegralType s)) :
    linearFlagEndpoints s q L (t :: ts) =
      (ChosenLatticeNeighbors.chosenLatticeNeighbors s q t L).bind (fun M => linearFlagEndpoints s q M ts) := by
  let : Fintype (Duality.LinearBlockFlags (q : ℤ_[q]) L (t :: ts)) := Fintype.ofFinite _
  let : Fintype (Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t) := Fintype.ofFinite _
  let : ∀ M : ChosenLatticeNeighbors.ChosenLatticePoint s q, Fintype (Duality.LinearBlockFlags (q : ℤ_[q]) M ts) :=
    fun _ => Fintype.ofFinite _
  let e := Duality.LinearBlockFlags.consEquiv (π := (q : ℤ_[q])) (L₀ := L) (t := t) (ts := ts)
  change (Finset.univ : Finset (Duality.LinearBlockFlags (q : ℤ_[q]) L (t :: ts))).val.map _ = _
  rw [← Multiset.map_univ_val_equiv e.symm, Multiset.map_map]
  change ((Finset.univ : Finset (Duality.LinearBlockFlags.NextChoices (q : ℤ_[q]) L t)).val.sigma
    (fun M => (Finset.univ : Finset (Duality.LinearBlockFlags (q : ℤ_[q]) (nextChoiceLattices s q M) ts)).val)).map
      (fun z => z.2.val (Fin.last ts.length)) = _
  rw [← nextChoices_enumeration s q L t]
  simp only [linearFlagEndpoints, Multiset.sigma, Multiset.map_bind, Multiset.map_map, Multiset.bind_map]
  rfl

theorem linearFlagEndpoints_single (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (t : Local.IntegralType s) :
    linearFlagEndpoints s q L [t] = ChosenLatticeNeighbors.chosenLatticeNeighbors s q t L := by
  rw [linearFlagEndpoints_cons]
  simp only [linearFlagEndpoints_nil]
  exact (Multiset.bind_singleton _ id).trans (Multiset.map_id _)

theorem linearFlagEndpoints_pair (L : ChosenLatticeNeighbors.ChosenLatticePoint s q) (u v : Local.IntegralType s) :
    linearFlagEndpoints s q L [u, v] =
      (ChosenLatticeNeighbors.chosenLatticeNeighbors s q u L).bind (ChosenLatticeNeighbors.chosenLatticeNeighbors s q v) := by
  rw [linearFlagEndpoints_cons]
  simp only [linearFlagEndpoints_single]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagEndpoints
