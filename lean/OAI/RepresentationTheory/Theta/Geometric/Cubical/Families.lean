import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyProducts
import OAI.RepresentationTheory.Theta.Geometric.Cubical.PullbackFactors

/-! # Families -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Generated theta families on the two cubical products. The original
cubical identity places both families in one common automorphy factor. -/

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData} {J K : Φ.AutomorphyFactor}

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.castFactor (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : J = K) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family K := by
  classical
  exact
    { degree := F.degree
      sections := F.sections.image (fun s => s.castFactor h)
      nonzero := fun z => by
        obtain ⟨s, hs, hsz⟩ := F.nonzero z
        refine ⟨s.castFactor h, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
        rwa [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castFactor_apply] }

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.castFactor_degree (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : J = K) : (F.castFactor h).degree = F.degree := rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.castFactor_mem (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : J = K) (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (hs : s ∈ F.sections) :
    s.castFactor h ∈ (F.castFactor h).sections := by
  classical
  exact Finset.mem_image.mpr ⟨s, hs, rfl⟩

variable (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (f g h : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice)
    (hg : ∀ l : Ψ.periodIntegerLattice, g l.val ∈ Φ.periodIntegerLattice)
    (hh : ∀ l : Ψ.periodIntegerLattice, h l.val ∈ Φ.periodIntegerLattice)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCubeWithDegree : {G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.leftCubeFactor f g h hf hg hh) // G.degree = F.degree} := by
  let F0 := F.comap (f + g + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem (f + g) h (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg) hh)
  let F1 := F.comap f hf
  let F2 := F.comap g hg
  let F3 := F.comap h hh
  let A := F0.factorMul F1 rfl
  have ha : A.degree = F.degree := AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_degree F0 F1 rfl
  let B := A.factorMul F2 ha.symm
  have hb : B.degree = F.degree := (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_degree A F2 ha.symm).trans ha
  exact ⟨B.factorMul F3 hb.symm, (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_degree B F3 hb.symm).trans hb⟩

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.leftCubeFactor f g h hf hg hh) :=
  (F.leftCubeWithDegree f g h hf hg hh).val

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCubeWithDegree : {G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.rightCubeFactor f g h hf hg hh) // G.degree = F.degree} := by
  let F0 := F.comap (f + g) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg)
  let F1 := F.comap (f + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f h hf hh)
  let F2 := F.comap (g + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem g h hg hh)
  let A := F0.factorMul F1 rfl
  have ha : A.degree = F.degree := AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_degree F0 F1 rfl
  exact ⟨A.factorMul F2 ha.symm, (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_degree A F2 ha.symm).trans ha⟩

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCube : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.rightCubeFactor f g h hf hg hh) :=
  (F.rightCubeWithDegree f g h hf hg hh).val

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_degree : (F.leftCube f g h hf hg hh).degree = F.degree :=
  (F.leftCubeWithDegree f g h hf hg hh).property

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCube_degree : (F.rightCube f g h hf hg hh).degree = F.degree :=
  (F.rightCubeWithDegree f g h hf hg hh).property

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCubeOnLeft (hJ : J.IsCubical) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.leftCubeFactor f g h hf hg hh) :=
  (F.rightCube f g h hf hg hh).castFactor (J.cubeFactors_eq f g h hf hg hh hJ).symm

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCubeOnLeft_degree (hJ : J.IsCubical) :
    (F.rightCubeOnLeft f g h hf hg hh hJ).degree = F.degree := by
  exact (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.castFactor_degree _ _).trans (F.rightCube_degree f g h hf hg hh)

end

end OAI.RepresentationTheory.Theta.Geometric
