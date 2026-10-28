import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelKernelHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainZeroCokernel

/-! # Kernel Tower Cech Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechHomology

noncomputable section

/-! Positive homology of the top-cohomology complex of a coherent kernel
tower, computed by the native Čech connecting morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))
  (T : KernelTowerResolution.Tower (C := X.Modules))
  [∀ n, (T.object n).IsQuasicoherent] [∀ n, (T.term n).IsQuasicoherent]

def complex (N : ℕ) : ChainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  ((TopCechRightExact.functor π U N).mapHomologicalComplex (.down ℕ)).obj T.complex

omit [X.IsSeparated] [Fintype ι] [∀ (n : ℕ), (T.object n).IsQuasicoherent] [∀ (n : ℕ), (T.term n).IsQuasicoherent] in
theorem complex_d (N n : ℕ) : (KernelTowerCechHomology.complex π U T N).d (n + 1) n =
    (TopCechRightExact.functor π U N).map (T.differential n) := by
  exact congrArg (fun f => (TopCechRightExact.functor π U N).map f) (T.complex_d n)

include hU

def zeroIso (N : ℕ) (hN : Fintype.card ι ≤ N + 1) :
    (KernelTowerCechHomology.complex π U T N).homology 0 ≅
      (TopCechRightExact.functor π U N).obj (T.object 0) := by
  let F := TopCechRightExact.functor π U N
  let K := KernelTowerCechHomology.complex π U T N
  let B := ShortComplex.mk (T.differential 0) (T.projection 0) (T.differential_projection 0)
  let p := F.map (T.projection 0)
  letI : Epi p := TopCechRightExact.map_epi π U hU N hN (T.projection 0)
  have hf : K.d 1 0 = F.map (T.differential 0) := KernelTowerCechHomology.complex_d π U T N 0
  have wp : K.d 1 0 ≫ p = 0 := by
    rw [hf]
    change F.map (T.differential 0) ≫ F.map (T.projection 0) = 0
    rw [← F.map_comp, T.differential_projection, F.map_zero]
  have hp : (ShortComplex.mk (K.d 1 0) p wp).Exact := by
    have : Epi B.g := T.epi 0
    let : B.X₁.IsQuasicoherent := inferInstanceAs ((T.term 1).IsQuasicoherent)
    let : B.X₂.IsQuasicoherent := inferInstanceAs ((T.term 0).IsQuasicoherent)
    let : B.X₃.IsQuasicoherent := inferInstanceAs ((T.object 0).IsQuasicoherent)
    have h := TopCechRightExact.map_exact π U hU N hN B (T.exact_projection 0)
    let e : B.map F ≅ ShortComplex.mk (K.d 1 0) p wp :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          change 𝟙 _ ≫ K.d 1 0 = F.map (T.differential 0) ≫ 𝟙 _
          simpa only [Category.id_comp, Category.comp_id] using hf)
        (by
          change 𝟙 _ ≫ p = p ≫ 𝟙 _
          simp)
    exact ShortComplex.exact_of_iso e h
  exact ChainZeroCokernel.iso K p wp hp

def positiveIso (n : ℕ) (hn : Fintype.card ι ≤ n + 2)
    (hz : ∀ i, IsZero ((TopCechRightExact.functor π U n).obj (T.term i))) (i : ℕ) :
    (KernelTowerCechHomology.complex π U T (n + 1)).homology (i + 1) ≅
      (TopCechRightExact.functor π U n).obj (T.object i) := by
  let F := TopCechRightExact.functor π U (n + 1)
  let K := KernelTowerCechHomology.complex π U T (n + 1)
  let A := K.sc' (i + 1 + 1) (i + 1) i
  let B := ShortComplex.mk (T.differential (i + 1)) (T.projection (i + 1))
    (T.differential_projection (i + 1))
  let p := F.map (T.projection (i + 1))
  let a := F.map (T.inclusion i)
  have hC := KernelTowerCechShift.sequence_shortExact π U hU T i
  let δ := hC.δ n (n + 1) (by simp)
  letI : Epi p := TopCechRightExact.map_epi π U hU (n + 1) hn (T.projection (i + 1))
  letI : Mono δ := hC.mono_δ n (n + 1) (by simp) (hz i)
  have hf : A.f = F.map (T.differential (i + 1)) := KernelTowerCechHomology.complex_d π U T (n + 1) (i + 1)
  have hg : A.g = F.map (T.differential i) := KernelTowerCechHomology.complex_d π U T (n + 1) i
  have wp : A.f ≫ p = 0 := by
    rw [hf]
    change F.map (T.differential (i + 1)) ≫ F.map (T.projection (i + 1)) = 0
    rw [← F.map_comp, T.differential_projection, F.map_zero]
  have hp : (ShortComplex.mk A.f p wp).Exact := by
    have : Epi B.g := T.epi (i + 1)
    let : B.X₁.IsQuasicoherent := inferInstanceAs ((T.term (i + 1 + 1)).IsQuasicoherent)
    let : B.X₂.IsQuasicoherent := inferInstanceAs ((T.term (i + 1)).IsQuasicoherent)
    let : B.X₃.IsQuasicoherent := inferInstanceAs ((T.object (i + 1)).IsQuasicoherent)
    have h := TopCechRightExact.map_exact π U hU (n + 1) hn B (T.exact_projection (i + 1))
    let e : B.map F ≅ ShortComplex.mk A.f p wp :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          change 𝟙 _ ≫ A.f = F.map (T.differential (i + 1)) ≫ 𝟙 _
          simpa only [Category.id_comp, Category.comp_id] using hf)
        (by
          change 𝟙 _ ≫ p = p ≫ 𝟙 _
          simp)
    exact ShortComplex.exact_of_iso e h
  have wδ : δ ≫ a = 0 := hC.δ_comp n (n + 1) (by simp)
  have hδ : (ShortComplex.mk δ a wδ).Exact := hC.homology_exact₁ n (n + 1) (by simp)
  have fac : p ≫ a = A.g := by
    rw [hg]
    exact (F.map_comp (T.projection (i + 1)) (T.inclusion i)).symm
  exact K.homologyIsoSc' (i + 1 + 1) (i + 1) i (by simp) (by simp) ≪≫
    CokernelKernelHomology.iso A p a δ wp hp wδ hδ fac

def shiftedPositiveIso (q i : ℕ) (hn : Fintype.card ι ≤ q + i + 2)
    (hz : ∀ r < q + i + 1, ∀ j,
      IsZero ((TopCechRightExact.functor π U r).obj (T.term j))) :
    (KernelTowerCechHomology.complex π U T (q + i + 1)).homology (i + 1) ≅
      (TopCechRightExact.functor π U q).obj (T.object 0) :=
  positiveIso π U hU T (q + i) hn (hz (q + i) (by omega)) i ≪≫
    (KernelTowerCechShift.iteratedShiftIso π U hU T q i
      (fun m hm => ⟨hz (q + m) (by omega) m, hz (q + m + 1) (by omega) m⟩)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechHomology
