import OAI.Analysis.Fourier.WavePackets.General.Family.Solution
import OAI.Analysis.Fourier.WavePackets.FlowInverse
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Pushback

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {Z T : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

def LocalDirichletFamily.flowInverse (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    (z : Z) (t : T) : E → E :=
  OAI.Analysis.Fourier.WavePackets.flowInverse H.map (fun y => G.backward (z,y)) t

omit [CompleteSpace T] in
theorem LocalDirichletFamily.flowInverse_map (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    (z : Z) {t : T} (ht : ‖t‖ < H.radius) (y : E) :
    H.map (t,G.flowInverse H z t y) = G.backward (z,y) :=
  Function.invFun_eq ((H.bijective t ht).surjective _)

omit [CompleteSpace T] in
theorem LocalDirichletFamily.flowInverse_into_closed (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    {z : Z} (hz : z ∈ U) {t : T} (ht : ‖t‖ < H.radius)
    {y : E} (hy : (D z).defining y ≤ 0) :
    (D z₀).defining (G.flowInverse H z t y) ≤ 0 := by
  apply (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily_preserves_closed_domain (H.bijective t ht) (H.closed_domain t ht) _).mpr
  exact G.backward_closed z hz y hy

omit [CompleteSpace T] in
theorem LocalDirichletFamily.flowInverse_into_domain (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    {z : Z} (hz : z ∈ U) {t : T} (ht : ‖t‖ < H.radius)
    {y : E} (hy : (D z).defining y < 0) :
    (D z₀).defining (G.flowInverse H z t y) < 0 := by
  apply (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily_preserves_domain (H.bijective t ht) (H.open_domain t ht) _).mpr
  exact G.backward_strict z hz y hy

omit [CompleteSpace T] in
theorem LocalDirichletFamily.flowInverse_into_boundary (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    {z : Z} (hz : z ∈ U) {t : T} (ht : ‖t‖ < H.radius)
    {y : E} (hy : (D z).defining y = 0) :
    (D z₀).defining (G.flowInverse H z t y) = 0 := by
  apply le_antisymm (G.flowInverse_into_closed H hz ht hy.le)
  by_contra hn
  have hnegative := (H.open_domain t ht (G.flowInverse H z t y)).mpr (lt_of_not_ge hn)
  rw [G.flowInverse_map H z ht y,G.backward_boundary hz hy] at hnegative
  exact (lt_irrefl 0) hnegative

omit [CompleteSpace T] in
theorem LocalDirichletFamily.flowInverse_contDiffAt (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    {z : Z} (hz : z ∈ U) {t : T} (ht : ‖t‖ < H.radius)
    {y : E} (hy : (D z).defining y ≤ 0) :
    ContDiffAt ℝ ∞ (G.flowInverse H z t) y := by
  exact (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiff_inverseFamily_slice (U := {s : T | ‖s‖ < H.radius})
    (Φ := H.map) H.inverse_smooth ht).contDiffAt.comp y
    (G.backward_slice_contDiffAt hz hy)

omit [CompleteSpace T] in
theorem LocalDirichletFamily.flowInverse_periodic (G : LocalDirichletFamily D z₀ U)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    (z : Z) {t : T} (ht : ‖t‖ < H.radius)
    (l : Submodule.span ℤ (range b)) (y : E) :
    G.flowInverse H z t (y+e.symm ((l:P),0)) =
      G.flowInverse H z t y + e.symm ((l:P),0) := by
  unfold OAI.Analysis.Fourier.WavePackets.LocalDirichletFamily.flowInverse OAI.Analysis.Fourier.WavePackets.flowInverse
  dsimp only
  rw [G.backward_periodic]
  exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily_equivariant t (H.bijective t ht) (e.symm ((l:P),0))
    (H.equivariant t l) _

end OAI.Analysis.Fourier.WavePackets
