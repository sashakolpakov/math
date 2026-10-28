import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveFlasque
import OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

/-! # Constant Sheaf Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections

noncomputable section

/-!
# Constant-sheaf morphisms are actual global sections

The equivalence is the constant-sheaf adjunction followed by evaluation at
one. Its linearity and naturality are proved for the actual section maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

variable {M : TopCat.{0}}

abbrev ComplexSheaves (M : TopCat.{0}) :=
  Sheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)

abbrev standardConstantSheaf (M : TopCat.{0}) : ComplexSheaves M :=
  (constantSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)

def constantHomSectionsEquiv (F : ComplexSheaves M) :
    (standardConstantSheaf M ⟶ F) ≃ F.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
    isTerminalTop).homEquiv (ModuleCat.of ℂ ℂ) F).trans
      ((ModuleCat.homLinearEquiv (R := ℂ) (S := ℂ)).toEquiv.trans
        (LinearMap.ringLmapEquivSelf ℂ ℂ _).toEquiv)

theorem constantHomSectionsEquiv_apply (F : ComplexSheaves M)
    (f : standardConstantSheaf M ⟶ F) :
    constantHomSectionsEquiv F f =
      ((constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
        isTerminalTop).homEquiv (ModuleCat.of ℂ ℂ) F f) 1 := rfl

def constantHomSectionsLinearEquiv (F : ComplexSheaves M) :
    (standardConstantSheaf M ⟶ F) ≃ₗ[ℂ] F.obj.obj (op ⊤) where
  toEquiv := constantHomSectionsEquiv F
  map_add' f g := by
    change constantHomSectionsEquiv F (f + g) =
      constantHomSectionsEquiv F f + constantHomSectionsEquiv F g
    simp only [constantHomSectionsEquiv_apply, Adjunction.homEquiv_unit]
    rfl
  map_smul' c f := by
    change constantHomSectionsEquiv F (c • f) = c • constantHomSectionsEquiv F f
    simp only [constantHomSectionsEquiv_apply, Adjunction.homEquiv_unit]
    rfl

theorem constantHomSectionsLinearEquiv_naturality
    {F G : ComplexSheaves M}
    (f : standardConstantSheaf M ⟶ F) (g : F ⟶ G) :
    constantHomSectionsLinearEquiv G (f ≫ g) =
      g.hom.app (op ⊤) (constantHomSectionsLinearEquiv F f) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
    isTerminalTop
  change (adj.homEquiv _ G (f ≫ g)) 1 = _
  rw [adj.homEquiv_naturality_right]
  rfl

theorem constantHomSectionsLinearEquiv_symm_naturality
    {F G : ComplexSheaves M}
    (s : F.obj.obj (op ⊤)) (g : F ⟶ G) :
    (constantHomSectionsLinearEquiv F).symm s ≫ g =
      (constantHomSectionsLinearEquiv G).symm (g.hom.app (op ⊤) s) := by
  apply (constantHomSectionsLinearEquiv G).injective
  rw [constantHomSectionsLinearEquiv_naturality]
  simp

def constantHomSectionsComplexIso (K : CochainComplex (ComplexSheaves M) ℕ) :
    ((((linearCoyoneda ℂ (ComplexSheaves M)).obj (op (standardConstantSheaf M))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) ≅
    ((((sheafSections (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).obj (op ⊤)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (constantHomSectionsLinearEquiv (K.X n)).toModuleIso)
    (fun i j _ => by
      ext f
      exact constantHomSectionsLinearEquiv_naturality f (K.d i j))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections
