import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFlags

/-! # Flag Recursion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagRecursion.SphericalPELAlbaneseData.PELFlag

noncomputable section

/-! Actual correspondence flags decompose into their first cover branch
and a flag starting at its target. Cover points are retained literally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {D : Data.SphericalPELAlbaneseData E K s q}
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)}
  {x : D.GeometricPoint b} {ts : List (Local.IntegralType s)}

@[ext]
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.ext {F G : D.PELFlag b x ts} (hp : F.point = G.point) (hb : F.branch = G.branch) : F = G := by
  cases F
  cases G
  cases hp
  cases hb
  rfl

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.nil (x : D.GeometricPoint b) : D.PELFlag b x [] where
  point _ := x
  start := rfl
  branch j := Fin.elim0 j
  source j := Fin.elim0 j
  target j := Fin.elim0 j

instance : Subsingleton (D.PELFlag b x []) := ⟨fun F G => by
  apply Data.SphericalPELAlbaneseData.PELFlag.ext
  · funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact F.start.trans G.start.symm
  · funext j
    exact Fin.elim0 j⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.nilEquiv (x : D.GeometricPoint b) : D.PELFlag b x [] ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Data.SphericalPELAlbaneseData.PELFlag.nil x
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl

variable {t : Local.IntegralType s}

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.cons (c : (D.correspondence t).Fiber x)
    (F : D.PELFlag b (c.val ≫ (D.correspondence t).target) ts) : D.PELFlag b x (t :: ts) where
  point := Fin.cases x F.point
  start := rfl
  branch := Fin.cases c.val F.branch
  source j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact c.property
    · exact F.source i
  target j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact F.start.symm
    · exact F.target i

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.first (F : D.PELFlag b x (t :: ts)) : (D.correspondence t).Fiber x :=
  ⟨F.branch 0, (F.source 0).trans F.start⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.tail (F : D.PELFlag b x (t :: ts)) :
    D.PELFlag b ((Data.SphericalPELAlbaneseData.PELFlag.first F).val ≫ (D.correspondence t).target) ts where
  point j := F.point j.succ
  start := (F.target 0).symm
  branch j := F.branch j.succ
  source j := F.source j.succ
  target j := F.target j.succ

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.cons_first_tail (F : D.PELFlag b x (t :: ts)) : Data.SphericalPELAlbaneseData.PELFlag.cons (Data.SphericalPELAlbaneseData.PELFlag.first F) (Data.SphericalPELAlbaneseData.PELFlag.tail F) = F := by
  apply Data.SphericalPELAlbaneseData.PELFlag.ext
  · funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact F.start.symm
    · rfl
  · funext j
    refine Fin.cases rfl (fun _ => rfl) j

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.PELFlag.consEquiv : D.PELFlag b x (t :: ts) ≃
    Σ c : (D.correspondence t).Fiber x, D.PELFlag b (c.val ≫ (D.correspondence t).target) ts where
  toFun F := ⟨Data.SphericalPELAlbaneseData.PELFlag.first F, Data.SphericalPELAlbaneseData.PELFlag.tail F⟩
  invFun G := Data.SphericalPELAlbaneseData.PELFlag.cons G.1 G.2
  left_inv := Data.SphericalPELAlbaneseData.PELFlag.cons_first_tail
  right_inv G := by
    rcases G with ⟨c, F⟩
    rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagRecursion.SphericalPELAlbaneseData.PELFlag
