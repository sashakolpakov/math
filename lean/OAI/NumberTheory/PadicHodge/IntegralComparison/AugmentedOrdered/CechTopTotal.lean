import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalInjectionElements
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

/-! # Cech Top Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopTotal

noncomputable section

/-! Full-intersection cocycles in the actual augmented Čech total.
At the last Čech index the total differential is precisely the
coefficient differential, with no sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type u} [CommRing R]
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (g : ℕ) (hg : Fintype.card ι = g)

local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor.bicomplex U K
local notation "T" => HomologicalComplex₂.total (OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor.bicomplex U K) (ComplexShape.up ℕ)

def topTotalInclusion (q N : ℕ) (hN : q + g = N) :
    (K.X q).obj (op (CechCoordinates.topObject U g hg)) ⟶ (T).X N :=
  CechCoordinates.topInclusion U (K.X q) g hg ≫ (B).ιTotal (.up ℕ) q g N hN

theorem topTotalInclusion_differential (q N N' : ℕ) (hN : q + g = N)
    (hnext : N + 1 = N') (x : (K.X q).obj (op (CechCoordinates.topObject U g hg))) :
    (T).d N N' (topTotalInclusion U K g hg q N hN x) =
      topTotalInclusion U K g hg (q + 1) N' (by omega)
        ((K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x) := by
  subst N'
  change (T).d N (N + 1) ((B).ιTotal (.up ℕ) q g N hN
    (CechCoordinates.topInclusion U (K.X q) g hg x)) = _
  rw [Module.TotalInjectionElements.differential (CechFunctor.bicomplex U K) q g N hN]
  have hzero : ((B).X q).d g (g + 1) = 0 := by
    change (Cech.complex U (K.X q)).d g (g + 1) = 0
    dsimp only [Cech.complex]
    rw [CochainComplex.of_d]
    exact CechCoordinates.differential_top U (K.X q) g hg
  have hz : ((B).X q).d g (g + 1) (CechCoordinates.topInclusion U (K.X q) g hg x) = 0 := by
    rw [hzero]
    rfl
  rw [hz, map_zero, smul_zero, add_zero]
  have h := ConcreteCategory.congr_hom
    (CechCoordinates.topInclusion_naturality U (K.X q) g hg (K.d q (q + 1))) x
  change (CechFunctor.objectMap U (K.d q (q + 1)) g) (CechCoordinates.topInclusion U (K.X q) g hg x) =
    CechCoordinates.topInclusion U (K.X (q + 1)) g hg ((K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x) at h
  change (B).ιTotal (.up ℕ) (q + 1) g (N + 1) _
    ((CechFunctor.objectMap U (K.d q (q + 1)) g) (CechCoordinates.topInclusion U (K.X q) g hg x)) = _
  rw [h]
  rfl

def topTotalCycle (q : ℕ) (x : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
    (hx : (K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x = 0) :
    Module.CochainClasses.cycles T (q + g) :=
  ⟨topTotalInclusion U K g hg q (q + g) rfl x, by
    change (T).d (q + g) (q + g + 1) _ = 0
    rw [topTotalInclusion_differential U K g hg q (q + g) (q + g + 1) rfl rfl,
      hx, map_zero]⟩

def topTotalClass (q : ℕ) (x : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
    (hx : (K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x = 0) : (T).homology (q + g) :=
  Module.CochainClasses.classMap T (q + g) (topTotalCycle U K g hg q x hx)

theorem topTotalClass_eq (q : ℕ)
    (x y : (K.X (q + 1)).obj (op (CechCoordinates.topObject U g hg)))
    (hx : (K.d (q + 1) (q + 2)).app (op (CechCoordinates.topObject U g hg)) x = 0)
    (hy : (K.d (q + 1) (q + 2)).app (op (CechCoordinates.topObject U g hg)) y = 0)
    (η : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
    (hη : (K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) η = x - y) :
    topTotalClass U K g hg (q + 1) x hx = topTotalClass U K g hg (q + 1) y hy := by
  apply sub_eq_zero.mp
  change Module.CochainClasses.classMap T (q + 1 + g) (topTotalCycle U K g hg _ x hx) -
    Module.CochainClasses.classMap T (q + 1 + g) (topTotalCycle U K g hg _ y hy) = 0
  rw [← map_sub, Module.CochainClasses.classMap_eq_zero_iff]
  have hprev : (ComplexShape.up ℕ).prev (q + 1 + g) = q + g := by
    have he : q + 1 + g = (q + g) + 1 := by omega
    rw [he]
    exact (ComplexShape.up ℕ).prev_eq' rfl
  rw [hprev]
  refine ⟨topTotalInclusion U K g hg q (q + g) rfl η, ?_⟩
  rw [topTotalInclusion_differential U K g hg q (q + g) (q + 1 + g) rfl (by omega), hη]
  exact map_sub _ x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopTotal
