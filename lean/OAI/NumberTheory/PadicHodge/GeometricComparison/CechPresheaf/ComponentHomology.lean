import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso

/-! # Component Homology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ComponentHomology.CechPresheafComponentHomology

noncomputable section

/-! Equality of the finitely relevant presheaf components suffices
to identify the induced map on an original Cech total homology group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

variable {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (f g : K ⟶ L) (i : ℕ)
  (h : ∀ q, q ≤ i → ∀ U, (f.f q).app U = (g.f q).app U)

include h in
theorem total_component : (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E f).f i =
    (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E g).f i := by
  let B := (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R E).obj K
  let D := (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R E).obj L
  let a := (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R E).map f
  let b := (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R E).map g
  apply HomologicalComplex₂.total.hom_ext
  intro q r hqr
  have hq : q ≤ i := by
    change q + r = i at hqr
    exact hqr ▸ Nat.le_add_right q r
  have hc : (a.f q).f r = (b.f q).f r := by
    change Limits.Pi.map (fun x : (E.obj (op ⦋r⦌)).I =>
      (f.f q).app (op ((E.obj (op ⦋r⦌)).obj x))) =
        Limits.Pi.map (fun x : (E.obj (op ⦋r⦌)).I =>
          (g.f q).app (op ((E.obj (op ⦋r⦌)).obj x)))
    congr 1
    funext x
    exact h q hq _
  exact (HomologicalComplex₂.ιTotal_map B D a (.up ℕ) q r i hqr).trans
    ((congrArg (fun x => x ≫ D.ιTotal (.up ℕ) q r i hqr) hc).trans
      (HomologicalComplex₂.ιTotal_map B D b (.up ℕ) q r i hqr).symm)

theorem homology_of_component {A : Type*} [Category* A] [Abelian A]
    {M N : CochainComplex A ℕ} (a b : M ⟶ N) (j : ℕ) (hab : a.f j = b.f j) :
    HomologicalComplex.homologyMap a j = HomologicalComplex.homologyMap b j := by
  have hc : HomologicalComplex.cyclesMap a j = HomologicalComplex.cyclesMap b j := by
    apply (cancel_mono (N.iCycles j)).mp
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i, hab]
  apply (cancel_epi (M.homologyπ j)).mp
  rw [HomologicalComplex.homologyπ_naturality, HomologicalComplex.homologyπ_naturality, hc]

include h in
theorem homology : HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E f) i =
    HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E g) i :=
  homology_of_component _ _ i (total_component R E f g i h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ComponentHomology.CechPresheafComponentHomology
