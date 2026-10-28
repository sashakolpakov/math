import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagRecursion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors

/-! # Geometric Flag Endpoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Enumerating actual geometric flags gives exactly the iterated
neighbor multiset, retaining repeated geometric endpoints. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))

instance Data.SphericalPELAlbaneseData.finitePELFlag (x : D.GeometricPoint b) (ts : List (Local.IntegralType s)) : Finite (D.PELFlag b x ts) := by
  induction ts generalizing x with
  | nil => exact Finite.of_equiv PUnit (Data.SphericalPELAlbaneseData.PELFlag.nilEquiv x).symm
  | cons t ts ih =>
    have : ∀ c : (D.correspondence t).Fiber x, Finite (D.PELFlag b (c.val ≫ (D.correspondence t).target) ts) :=
      fun c => ih (c.val ≫ (D.correspondence t).target)
    exact Finite.of_equiv _ (Data.SphericalPELAlbaneseData.PELFlag.consEquiv (D := D) (x := x) (t := t) (ts := ts)).symm

def Data.SphericalPELAlbaneseData.geometricFlagEndpoints (x : D.GeometricPoint b) (ts : List (Local.IntegralType s)) : Multiset (D.GeometricPoint b) :=
  let : Fintype (D.PELFlag b x ts) := Fintype.ofFinite _
  (Finset.univ : Finset (D.PELFlag b x ts)).val.map (fun F => F.point (Fin.last ts.length))

theorem Data.SphericalPELAlbaneseData.geometricFlagEndpoints_nil (x : D.GeometricPoint b) : D.geometricFlagEndpoints b x [] = {x} := by
  let : Fintype (D.PELFlag b x []) := Fintype.ofFinite _
  have hu : (Finset.univ : Finset (D.PELFlag b x [])) = {Data.SphericalPELAlbaneseData.PELFlag.nil x} := by
    ext F
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  change (Finset.univ : Finset (D.PELFlag b x [])).val.map _ = _
  rw [hu]
  rfl

theorem Data.SphericalPELAlbaneseData.geometricFlagEndpoints_cons (x : D.GeometricPoint b) (t : Local.IntegralType s) (ts : List (Local.IntegralType s)) :
    D.geometricFlagEndpoints b x (t :: ts) =
      (D.neighbors t b x).bind (fun y => D.geometricFlagEndpoints b y ts) := by
  let : Fintype (D.PELFlag b x (t :: ts)) := Fintype.ofFinite _
  let : Fintype ((D.correspondence t).Fiber x) := Fintype.ofFinite _
  let : ∀ y : D.GeometricPoint b, Fintype (D.PELFlag b y ts) := fun _ => Fintype.ofFinite _
  let e := Data.SphericalPELAlbaneseData.PELFlag.consEquiv (D := D) (x := x) (t := t) (ts := ts)
  change (Finset.univ : Finset (D.PELFlag b x (t :: ts))).val.map _ = _
  rw [← Multiset.map_univ_val_equiv e.symm, Multiset.map_map]
  change ((Finset.univ : Finset ((D.correspondence t).Fiber x)).val.sigma
    (fun c => (Finset.univ : Finset (D.PELFlag b (c.val ≫ (D.correspondence t).target) ts)).val)).map
      (fun z => z.2.point (Fin.last ts.length)) = _
  simp only [Data.SphericalPELAlbaneseData.geometricFlagEndpoints, Data.SphericalPELAlbaneseData.neighbors, Correspondences.EtaleCorrespondence.neighbors,
    Multiset.sigma, Multiset.map_bind, Multiset.map_map, Multiset.bind_map]
  rfl

theorem Data.SphericalPELAlbaneseData.geometricFlagEndpoints_single (x : D.GeometricPoint b) (t : Local.IntegralType s) :
    D.geometricFlagEndpoints b x [t] = D.neighbors t b x := by
  rw [Data.SphericalPELAlbaneseData.geometricFlagEndpoints_cons]
  simp only [Data.SphericalPELAlbaneseData.geometricFlagEndpoints_nil]
  exact (Multiset.bind_singleton _ id).trans (Multiset.map_id _)

theorem Data.SphericalPELAlbaneseData.geometricFlagEndpoints_pair (x : D.GeometricPoint b) (u v : Local.IntegralType s) :
    D.geometricFlagEndpoints b x [u, v] = (D.neighbors u b x).bind (D.neighbors v b) := by
  rw [Data.SphericalPELAlbaneseData.geometricFlagEndpoints_cons]
  simp only [Data.SphericalPELAlbaneseData.geometricFlagEndpoints_single]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
