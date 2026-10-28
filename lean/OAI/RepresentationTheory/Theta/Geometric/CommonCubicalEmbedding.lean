import OAI.RepresentationTheory.Theta.Geometric.TripleEmbedding
import OAI.RepresentationTheory.Theta.Geometric.PowerAlgebraization

/-! # Common Cubical Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! One original theta embedding algebraizes a common family containing
both cubical products on any chosen triple-period abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonCubeModel_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonCubeModel_smooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extendFamily (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : G.degree = F.degree) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J := by
  classical
  exact F.extend (G.sections.image (fun s => s.castDegree h))

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extendFamily_degree (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : G.degree = F.degree) :
    (F.extendFamily G h).degree = F.degree := rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extendFamily_mem_right (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : G.degree = F.degree)
    (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J G.degree) (hs : s ∈ G.sections) :
    s.castDegree h ∈ (F.extendFamily G h).sections := by
  classical
  exact F.mem_extend_right _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extendFamily_injective (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : G.degree = F.degree)
    (hF : Function.Injective F.projectiveMap) : Function.Injective (F.extendFamily G h).projectiveMap :=
  F.extend_injective _ hF

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extendFamily_detects (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (h : G.degree = F.degree)
    (p v : Φ.space) (hF : F.Detects p v) : (F.extendFamily G h).Detects p v :=
  F.extend_detects _ p v hF

variable (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.tripleCube_degree : F.tripleCube.degree = F.degree :=
  F.leftCube_degree Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonTripleCube : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.leftCubeFactor Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem) :=
  F.tripleCube.extendFamily
    (F.rightCubeOnLeft Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
      Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem hJ)
    ((F.rightCubeOnLeft_degree Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
      Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem hJ).trans F.tripleCube_degree.symm)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonTripleCube_injective (hF : Function.Injective F.projectiveMap) :
    Function.Injective (F.commonTripleCube hJ).projectiveMap :=
  F.tripleCube.extendFamily_injective _ _ (F.tripleCube_injective hF)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonTripleCube_detects (hF : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (p v : Φ.triple.space) (hv : v ≠ 0) : (F.commonTripleCube hJ).Detects p v :=
  F.tripleCube.extendFamily_detects _ _ p v (F.tripleCube_detects hF p v hv)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonTripleCube_algebraic_embedding
    (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.triple.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.triple.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hA : ∀ u v, e (u + v) = e u * e v) :
    ∃ f : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonTripleCube hJ).projectiveDimension),
      IsClosedImmersion f.left ∧ ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
        AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonTripleCube hJ).projectiveDimension
          ((F.commonTripleCube hJ).projectiveMap t) :=
  (F.commonTripleCube hJ).algebraic_embedding_on_model (F.commonTripleCube_injective hJ hFi)
    (F.commonTripleCube_detects hJ hFd) A e hA

end

end OAI.RepresentationTheory.Theta.Geometric
