import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality

/-! # Matching Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule

noncomputable section

/-! The matching-section sheaf recovers every original local module.
Consequently actual line objects, rather than merely their classes,
descend along an open cover with specified coherent transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : MatchingSheaf.OpenModuleTransitions U M)

def MatchingSheaf.OpenModuleTransitions.evaluation (V : X.Opens) (i : ι) (hV : V ≤ U i) :
    D.sections V →ₗ[Γ(X, V)] Γ(M i, V) where
  toFun s := (M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.val i)
  map_add' s t := map_add _ _ _
  map_smul' r s := by
    let si : Γ(M i, V ⊓ U i) := s.val i
    let a : V ≤ V ⊓ U i := le_inf le_rfl hV
    let b : V ⊓ U i ≤ V := inf_le_left
    change (M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op
        (@SMul.smul Γ(X, V ⊓ U i) Γ(M i, V ⊓ U i) inferInstance
          (X.presheaf.map (homOfLE b).op r) si) =
      r • (M i).presheaf.map (homOfLE a).op si
    have hr : X.presheaf.map (homOfLE a).op (X.presheaf.map (homOfLE b).op r) = r :=
      (Relative.OpenFunctionUnits.openFunction_restriction_comp b a r).trans
        (ConcreteCategory.congr_hom (X.presheaf.map_id (.op V)) r)
    exact (Scheme.Modules.map_smul (M i) (homOfLE a) _ si).trans
      (congrArg (fun z : Γ(X, V) => z • (M i).presheaf.map (homOfLE a).op si) hr)

def MatchingSheaf.OpenModuleTransitions.generatorTuple (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : Γ(M i, V)) : MatchingSheaf.OpenModuleTransitions.Tuple U M V :=
  fun j => D.compare (V ⊓ U j) i j (inf_le_left.trans hV) inf_le_right
    ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op s)

theorem MatchingSheaf.OpenModuleTransitions.generatorTuple_mem (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : Γ(M i, V)) :
    D.generatorTuple V i hV s ∈ D.sections V := by
  intro j k
  let Q := (V ⊓ U j) ⊓ U k
  have qV : Q ≤ V := inf_le_left.trans inf_le_left
  have qj : Q ≤ V ⊓ U j := inf_le_left
  have qk : Q ≤ V ⊓ U k := le_inf qV inf_le_right
  have hj : (M j).presheaf.map (homOfLE qj).op (D.generatorTuple V i hV s j) =
      D.compare Q i j (qV.trans hV) (inf_le_left.trans inf_le_right)
        ((M i).presheaf.map (homOfLE qV).op s) :=
    (D.natural (V ⊓ U j) Q qj i j _ _ _).symm.trans
      (congrArg (D.compare Q i j _ _) (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _))
  have hk : (M k).presheaf.map (homOfLE qk).op (D.generatorTuple V i hV s k) =
      D.compare Q i k (qV.trans hV) inf_le_right
        ((M i).presheaf.map (homOfLE qV).op s) :=
    (D.natural (V ⊓ U k) Q qk i k _ _ _).symm.trans
      (congrArg (D.compare Q i k _ _) (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _))
  exact (congrArg (D.compare Q j k _ _) hj).trans
    ((D.composition Q i j k _ _ _ _).trans hk.symm)

def MatchingSheaf.OpenModuleTransitions.generator (V : X.Opens) (i : ι) (hV : V ≤ U i) :
    Γ(M i, V) →ₗ[Γ(X, V)] D.sections V where
  toFun s := ⟨D.generatorTuple V i hV s, D.generatorTuple_mem V i hV s⟩
  map_add' s t := by
    apply Subtype.ext
    funext j
    change D.compare _ _ _ _ _ ((M i).presheaf.map _ (s + t)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r s := by
    apply Subtype.ext
    funext j
    change D.compare (V ⊓ U j) i j _ _
        ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op (r • s)) =
      (X.presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op r) •
        D.compare (V ⊓ U j) i j _ _
          ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op s)
    rw [Scheme.Modules.map_smul, map_smul]

theorem MatchingSheaf.OpenModuleTransitions.evaluation_generator (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : Γ(M i, V)) :
    D.evaluation V i hV (D.generator V i hV s) = s := by
  change (M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op
    (D.compare (V ⊓ U i) i i _ _
      ((M i).presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op s)) = s
  rw [D.identity, MatchingSheaf.OpenModuleTransitions.restriction_comp, MatchingSheaf.OpenModuleTransitions.restriction_self]

theorem MatchingSheaf.OpenModuleTransitions.generator_evaluation (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : D.sections V) :
    D.generator V i hV (D.evaluation V i hV s) = s := by
  apply Subtype.ext
  funext j
  let Q := (V ⊓ U i) ⊓ U j
  have hQ : V ⊓ U j ≤ Q := le_inf (le_inf inf_le_left (inf_le_left.trans hV)) inf_le_right
  have he := congrArg ((M j).presheaf.map (homOfLE hQ).op) (s.property i j)
  have hl : D.generatorTuple V i hV (D.evaluation V i hV s) j =
      (M j).presheaf.map (homOfLE hQ).op
        (D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
          ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op (s.val i))) := by
    change D.compare (V ⊓ U j) i j _ _
        ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op
          ((M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.val i))) = _
    rw [← D.natural Q (V ⊓ U j) hQ i j]
    congr 1
    exact (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).trans (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).symm
  exact hl.trans (he.trans ((MatchingSheaf.OpenModuleTransitions.restriction_comp (M j) _ _ _).trans (MatchingSheaf.OpenModuleTransitions.restriction_self (M j) _ _ _)))

def MatchingSheaf.OpenModuleTransitions.evaluationEquiv (V : X.Opens) (i : ι) (hV : V ≤ U i) :
    D.sections V ≃ₗ[Γ(X, V)] Γ(M i, V) where
  __ := D.evaluation V i hV
  invFun := D.generator V i hV
  left_inv := D.generator_evaluation V i hV
  right_inv := D.evaluation_generator V i hV

theorem MatchingSheaf.OpenModuleTransitions.evaluation_natural {V W : X.Opens} (h : W ≤ V) (i : ι) (hV : V ≤ U i)
    (s : D.sections V) :
    D.evaluation W i (h.trans hV) (D.sectionRestriction h s) =
      (M i).presheaf.map (homOfLE h).op (D.evaluation V i hV s) := by
  exact (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).trans (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).symm

theorem MatchingSheaf.OpenModuleTransitions.evaluation_generator_other (V : X.Opens) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(M i, V)) :
    D.evaluation V j hj (D.generator V i hi s) = D.compare V i j hi hj s := by
  change (M j).presheaf.map (homOfLE (le_inf le_rfl hj)).op
    (D.compare (V ⊓ U j) i j _ _
      ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op s)) = _
  rw [← D.natural (V ⊓ U j) V (le_inf le_rfl hj) i j,
    MatchingSheaf.OpenModuleTransitions.restriction_comp, MatchingSheaf.OpenModuleTransitions.restriction_self]

/-- The local recovery maps realize the specified overlap comparison. -/
theorem MatchingSheaf.OpenModuleTransitions.evaluation_compare (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : D.sections V) :
    D.compare V i j hi hj (D.evaluation V i hi s) = D.evaluation V j hj s :=
  (D.evaluation_generator_other V i j hi hj (D.evaluation V i hi s)).symm.trans
    (congrArg (D.evaluation V j hj) (D.generator_evaluation V i hi s))

local instance MatchingSheaf.OpenModuleTransitions.matchingRestrictionModule (i : ι) (W : (U i).toScheme.Opensᵒᵖ) :
    Module Γ((U i).toScheme, W.unop) ((D.moduleSheaf.restrict (U i).ι).val.obj W) :=
  ((D.moduleSheaf.restrict (U i).ι).val.obj W).isModule

local instance MatchingSheaf.OpenModuleTransitions.originalRestrictionModule (i : ι) (W : (U i).toScheme.Opensᵒᵖ) :
    Module Γ((U i).toScheme, W.unop) (((M i).restrict (U i).ι).val.obj W) :=
  (((M i).restrict (U i).ι).val.obj W).isModule

def MatchingSheaf.OpenModuleTransitions.recoveryHom (i : ι) : D.moduleSheaf.restrict (U i).ι ⟶ (M i).restrict (U i).ι where
  val.app W := ModuleCat.ofHom
    (X := (D.moduleSheaf.restrict (U i).ι).val.obj W)
    (Y := ((M i).restrict (U i).ι).val.obj W)
    { toFun := D.evaluation ((U i).ι ''ᵁ W.unop) i (OpenFrame.LocalSections.openInclusionImage_le (U i) W.unop)
      map_add' s t := (D.evaluation ((U i).ι ''ᵁ W.unop) i
        (OpenFrame.LocalSections.openInclusionImage_le (U i) W.unop)).map_add s t
      map_smul' r s := by
        exact (D.evaluation ((U i).ι ''ᵁ W.unop) i
          (OpenFrame.LocalSections.openInclusionImage_le (U i) W.unop)).map_smul
            (((U i).ι.appIso W.unop).inv r) s }
  val.naturality {V W} f := by
    ext s
    exact D.evaluation_natural ((U i).ι.image_mono f.unop.le) i
      (OpenFrame.LocalSections.openInclusionImage_le (U i) V.unop) s

instance MatchingSheaf.OpenModuleTransitions.recoveryHom_isIso (i : ι) : IsIso (D.recoveryHom i) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (D.evaluation ((U i).ι ''ᵁ W) i (OpenFrame.LocalSections.openInclusionImage_le (U i) W))
  exact (D.evaluationEquiv ((U i).ι ''ᵁ W) i (OpenFrame.LocalSections.openInclusionImage_le (U i) W)).bijective

/-- The descended module restricts to the original local module. -/
def MatchingSheaf.OpenModuleTransitions.recoveryIso (i : ι) : D.moduleSheaf.restrict (U i).ι ≅ (M i).restrict (U i).ι :=
  asIso (D.recoveryHom i)

variable (hU : ∀ x : X, ∃ i, x ∈ U i)
  (L : ∀ i, Line.Bundles.LineBundle (U i).toScheme)
  (r : ∀ i, (M i).restrict (U i).ι ≅ (L i).sheaf)

def MatchingSheaf.OpenModuleTransitions.localLineRecovery (i : ι) :
    (Scheme.Modules.pullback (U i).ι).obj D.moduleSheaf ≅ (L i).sheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app D.moduleSheaf ≪≫
    D.recoveryIso i ≪≫ r i

/-- Coherent local line objects produce an actual global line bundle. -/
def MatchingSheaf.OpenModuleTransitions.lineBundle : Line.Bundles.LineBundle X where
  sheaf := D.moduleSheaf
  locallyTrivial := by
    apply Picard.PoincareBundle.Line.Locality.isLine_of_locally_isLine
    intro x
    obtain ⟨i, hi⟩ := hU x
    refine ⟨U i, hi, ?_⟩
    exact Picard.PoincareBundle.Line.Bundles.IsLine.of_iso (L i).locallyTrivial
      (D.localLineRecovery L r i).symm

def MatchingSheaf.OpenModuleTransitions.lineBundle_recovery (i : ι) :
    ((D.lineBundle hU L r).pullback (U i).ι).sheaf ≅ (L i).sheaf :=
  D.localLineRecovery L r i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule
