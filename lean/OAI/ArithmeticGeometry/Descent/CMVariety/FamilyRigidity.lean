import OAI.ArithmeticGeometry.Descent.CMVariety.ConcreteFiberLevelRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancementExtension

/-! # Family Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FamilyRigidity.Abelian

noncomputable section

/-!
Use any prescribed central geometric presentation and preserve additional
global endomorphisms. The CM tuple is chosen and spread first; adjoining
the already defined endomorphisms preserves its proved period rigidity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj _root_.Topology

def replaceFiberPresentation {Index : Type} {g : ℕ}
    (G : Index → AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (present : ∀ i, StandardModuli.Abelian.ComplexAbelianPresentation (G i))
    (i₀ : Index) (P : StandardModuli.Abelian.ComplexAbelianPresentation (G i₀)) :
    ∀ i, StandardModuli.Abelian.ComplexAbelianPresentation (G i) :=
  Function.update present i₀ P

@[simp]
theorem replaceFiberPresentation_self {Index : Type} {g : ℕ}
    (G : Index → AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (present : ∀ i, StandardModuli.Abelian.ComplexAbelianPresentation (G i))
    (i₀ : Index) (P : StandardModuli.Abelian.ComplexAbelianPresentation (G i₀)) :
    replaceFiberPresentation G present i₀ P i₀ = P := by
  simp only [replaceFiberPresentation, Function.update_self]

namespace FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom] {g : ℕ}

theorem smooth_family_fixed_center_tuple_rigid
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (n : ℕ) (hn : 0 < n) (level : G.FullLevel n) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s₀.left)) (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety)
    (k : Fin E.size → (G.scheme ⟶ G.scheme)) (hk : ∀ i, IsMonHom (k i))
    (hk₀ : ∀ i, P.comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s₀ ≫ P.comparison.hom = E.map i) :
    ∀ᶠ s in 𝓝 s₀, ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso G level k s₀ s := by
  let present' := replaceFiberPresentation (fun s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S => G.pullback s.left) present s₀ P
  have H := ConcreteFiberLevelRigidity.Abelian.FamilyPoints.smooth_fixed_tuple_locally_isomorphic_with_level G present' n hn level s₀
  have hp : present' s₀ = P := replaceFiberPresentation_self _ _ _ _
  rw [hp] at H
  exact H E k hk hk₀

theorem smooth_family_preserves_retained_endomorphisms
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (n : ℕ) (hn : 0 < n) (level : G.FullLevel n) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s₀.left)) (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin E.size) G)
    (hk₀ : ∀ i, P.comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k.map i) s₀ ≫ P.comparison.hom = E.map i)
    {r : ℕ} (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin r) G) :
    ∀ᶠ s in 𝓝 s₀, ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso G level a.map s₀ s := by
  let a₀ (i : Fin r) := P.comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (a.map i) s₀ ≫ P.comparison.hom
  have ha₀ (i : Fin r) : IsMonHom (a₀ i) := by
    let : IsMonHom (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (a.map i) s₀) := FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G (a.map i) s₀
    dsimp only [a₀]
    infer_instance
  let E' := E.append a₀ ha₀
  let combined := k.append a
  have hcombined (i : Fin E'.size) :
      P.comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (combined.map i) s₀ ≫ P.comparison.hom = E'.map i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [combined, AbelianEndomorphism.AbelianEndomorphismTuple.append, E', AlgebraicEnhancement.Abelian.CMEnhancement.append,
        Fin.addCases_left] using hk₀ j
    · intro j
      simp only [combined, AbelianEndomorphism.AbelianEndomorphismTuple.append, E', AlgebraicEnhancement.Abelian.CMEnhancement.append,
        Fin.addCases_right]
      rfl
  have h := smooth_family_fixed_center_tuple_rigid G present n hn level s₀ P E'
    combined.map combined.group hcombined
  filter_upwards [h] with s hs
  obtain ⟨e, he, hmaps, hlevel⟩ := hs
  refine ⟨e, he, fun i => ?_, hlevel⟩
  simpa only [combined, AbelianEndomorphism.AbelianEndomorphismTuple.append, Fin.addCases_right] using
    hmaps (Fin.natAdd E.size i)

end FamilyPoints

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FamilyRigidity.Abelian
