import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Splitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericParameters

/-! # Characters -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Characters.Lifts

noncomputable section

/-!
Construct every integral graph character from its evaluated generic
linear map. The domains are native constant group schemes, and the
generic coordinate formula is proved from unique extension of labels.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

section ConstantCoordinates

universe u

variable {S : Scheme.{u}} (G : Type u) [Group G]
variable (T : Over S) [PreconnectedSpace T.left] (t₀ : T.left)

def locallyConstantEvaluationEquiv : LocallyConstant T.left G ≃* G where
  toFun c := c t₀
  invFun := LocallyConstant.const T.left
  left_inv c := (c.eq_const t₀).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

def constantPointCoordinates : (T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) ≃* G :=
  ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op T)).groupIsoToMulEquiv.trans
    (locallyConstantEvaluationEquiv G T t₀)

theorem constantPointCoordinates_factor (a : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :
    a = toUnit T ≫ ConstantSections.Lifts.constantLabelSection S G (constantPointCoordinates G T t₀ a) := by
  apply ConstantSections.Lifts.constantPoint_factor
  intro t
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T a).apply_eq_of_preconnectedSpace t t₀

end ConstantCoordinates

variable (R L : Type) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
variable (M : Over (Spec (.of R))) [GrpObj M] [IsProper M.hom]
variable (m : (Sections.Lifts.genericTest R L ⟶ M) ≃* Multiplicative F)

local instance genericTest_preconnected : PreconnectedSpace (Sections.Lifts.genericTest R L).left :=
  inferInstanceAs (PreconnectedSpace (Spec (.of L)))

def evaluatedLinearLabels (U : Submodule F V) (f : U →ₗ[F] F) :
    Multiplicative U →* (Sections.Lifts.genericTest R L ⟶ M) :=
  m.symm.toMonoidHom.comp f.toAddMonoidHom.toMultiplicative

/-- The graph character is an actual integral group-scheme morphism,
constructed from evaluated generic points by properness. -/
def evaluatedGraphCharacter (U : Submodule F V) (f : U →ₗ[F] F) :
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X ⟶ M :=
  Splitting.Lifts.evaluatedConstantMap R L M (evaluatedLinearLabels R L M m U f)

instance evaluatedGraphCharacter_isMonHom (U : Submodule F V) (f : U →ₗ[F] F) :
    IsMonHom (evaluatedGraphCharacter R L M m U f) :=
  inferInstanceAs (IsMonHom (Splitting.Lifts.evaluatedConstantMap R L M (evaluatedLinearLabels R L M m U f)))

def genericConstantCoordinates (G : Type) [Group G] :
    (Sections.Lifts.genericTest R L ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X) ≃* G :=
  constantPointCoordinates G (Sections.Lifts.genericTest R L) (IsLocalRing.closedPoint L)

/-- The coordinate equation of the constructed graph is derived, so it
does not need to be supplied to the generic subgroup enumeration theorem. -/
theorem evaluatedGraphCharacter_coordinates (U : Submodule F V) (f : U →ₗ[F] F)
    (a : Sections.Lifts.genericTest R L ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X) :
    (m (a ≫ evaluatedGraphCharacter R L M m U f)).toAdd =
      f ((genericConstantCoordinates R L (Multiplicative U) a).toAdd) := by
  have ha := constantPointCoordinates_factor (Multiplicative U) (Sections.Lifts.genericTest R L)
    (IsLocalRing.closedPoint L) a
  have h := Splitting.Lifts.evaluatedConstantMap_generic_labels R L M (evaluatedLinearLabels R L M m U f)
    (genericConstantCoordinates R L (Multiplicative U) a)
  change (toUnit (Sections.Lifts.genericTest R L) ≫ ConstantSections.Lifts.constantLabelSection (Spec (.of R)) (Multiplicative U)
    (genericConstantCoordinates R L (Multiplicative U) a)) ≫
      evaluatedGraphCharacter R L M m U f =
    m.symm (Multiplicative.ofAdd (f ((genericConstantCoordinates R L (Multiplicative U) a).toAdd))) at h
  calc
    (m (a ≫ evaluatedGraphCharacter R L M m U f)).toAdd =
        (m ((toUnit (Sections.Lifts.genericTest R L) ≫ ConstantSections.Lifts.constantLabelSection (Spec (.of R)) (Multiplicative U)
          (genericConstantCoordinates R L (Multiplicative U) a)) ≫
            evaluatedGraphCharacter R L M m U f)).toAdd :=
      congrArg (fun x => (m (x ≫ evaluatedGraphCharacter R L M m U f)).toAdd) ha
    _ = _ := by rw [h, m.apply_symm_apply]; rfl

/-- The etale inclusion is independently induced by the literal submodule
inclusion of its label group. -/
def evaluatedEtaleInclusion (U : Submodule F V) :
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X ⟶
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative V)).X :=
  (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap (Spec (.of R)) U.subtype.toAddMonoidHom.toMultiplicative).hom.hom

omit [IsDomain R] [ValuationRing R] [IsFractionRing R L] in
theorem evaluatedEtaleInclusion_coordinates (U : Submodule F V)
    (a : Sections.Lifts.genericTest R L ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X) :
    (genericConstantCoordinates R L (Multiplicative V) (a ≫ evaluatedEtaleInclusion R U)).toAdd =
      ((genericConstantCoordinates R L (Multiplicative U) a).toAdd).val :=
  congrArg Multiplicative.toAdd
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap_sections (Spec (.of R)) U.subtype.toAddMonoidHom.toMultiplicative
      (Sections.Lifts.genericTest R L) a (IsLocalRing.closedPoint L))

/-- Every generic active subspace is obtained exactly by the constructed
graph/product kernel. All graph maps and both coordinate equations have
been built above, rather than supplied as enumeration input. -/
theorem evaluated_subspace_kernel_image (J : Submodule F (V × F)) :
    GenericParameters.kernelPointImage (m.toEquiv.trans Multiplicative.toAdd)
      ((genericConstantCoordinates R L (Multiplicative V)).toEquiv.trans Multiplicative.toAdd)
      (Intrinsic.Neighbors.subspaceKernel
        (fun U : Submodule F V => (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative U)).X)
        (𝟙 (M ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative V)).X))
        (evaluatedEtaleInclusion R) (evaluatedGraphCharacter R L M m) J) = (J : Set (V × F)) :=
  GenericParameters.generic_subspace_kernel_image _ _ _ _ _
    (fun U => (genericConstantCoordinates R L (Multiplicative U)).toEquiv.trans Multiplicative.toAdd)
    (fun U a => evaluatedEtaleInclusion_coordinates R L U a)
    (fun U f a => evaluatedGraphCharacter_coordinates R L M m U f a) J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Characters.Lifts
