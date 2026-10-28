import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyKernelCokernel
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.SecondShift

/-! # One Second -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.OneSecond

noncomputable section

/-! Native Tor in degree one is the kernel of tensoring the inclusion
in a projective presentation of its second argument. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

variable (R : Type u) [CommRing R] (N : ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) [Projective S.X₂]

def kernelIso : (((Tor (ModuleCat R) 1).obj N).obj S.X₃) ≅
    ModuleCat.of R ((tensorLeft N).map S.f).hom.ker := by
  let Q := projectiveResolution S.X₁
  let P := ResolutionAugment.resolution S hS Q
  let F := tensorLeft N
  let : HasKernel (F.map S.f) := HasLimit.mk ⟨_, ModuleCat.kernelIsLimit (F.map S.f)⟩
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let T := K.sc' 2 1 0
  have wp : T.f ≫ F.map (Q.π.f 0) = 0 := by
    change F.map (Q.complex.d 1 0) ≫ F.map (Q.π.f 0) = 0
    rw [← F.map_comp, Q.complex_d_comp_π_f_zero, F.map_zero]
  have hp : IsColimit (CokernelCofork.ofπ (F.map (Q.π.f 0)) wp) :=
    CokernelCofork.mapIsColimit _ Q.isColimitCokernelCofork F
  have hg : F.map (Q.π.f 0) ≫ F.map S.f = T.g := by
    change F.map (Q.π.f 0) ≫ F.map S.f = F.map (Q.π.f 0 ≫ S.f)
    rw [F.map_comp]
  exact P.isoLeftDerivedObj F 1 ≪≫ K.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    HomologyKernelCokernel.homologyIsoKernel T (F.obj S.X₁) (F.map (Q.π.f 0)) wp hp
      (F.map S.f) hg ≪≫ ModuleCat.kernelIsoKer (F.map S.f)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.OneSecond
