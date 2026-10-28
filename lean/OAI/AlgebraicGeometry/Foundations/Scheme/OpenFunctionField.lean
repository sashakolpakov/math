import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension

/-! # Open Function Field -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

noncomputable section

/-!
# Function fields and dimensions under nonempty open immersions

The function-field isomorphism is the actual stalk isomorphism of the open
immersion at the generic point, transported along the proved equality of
generic points. Its compatibility with scalar constants is proved from the
germ/stalk-map identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {Y X : Scheme.{u}} [IrreducibleSpace Y] [IrreducibleSpace X]

/-- An open immersion identifies the actual generic stalks. -/
def openImmersionFunctionFieldIso (i : Y ⟶ X) [IsOpenImmersion i] :
    X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion i).symm) ≪≫
    asIso (i.stalkMap (genericPoint Y))

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic-stalk isomorphism commutes with taking germs of global sections. -/
theorem openImmersionFunctionFieldIso_germ (i : Y ⟶ X) [IsOpenImmersion i] :
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫ (openImmersionFunctionFieldIso i).hom =
      i.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact i.germ_stalkMap ⊤ (genericPoint Y) (by trivial)

/-- Compatibility with the original global-functions base map is a genuine
consequence of functoriality of pullback and of germs. -/
theorem openImmersionFunctionFieldIso_base {S : Scheme.{u}}
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ S) :
    Betti.AffineDimension.Realization.functionFieldBaseMap f ≫ (openImmersionFunctionFieldIso i).hom =
      Betti.AffineDimension.Realization.functionFieldBaseMap (i ≫ f) := by
  simp only [Betti.AffineDimension.Realization.functionFieldBaseMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [openImmersionFunctionFieldIso_germ]

variable {K : Type u} [Field K]

/-- The generic-stalk isomorphism respects the canonical scalar map. -/
theorem openImmersionFunctionFieldIso_scalar
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of K)) :
    (openImmersionFunctionFieldIso i).hom.hom.comp (FunctionFieldScalar.functionFieldScalarMap f) =
      FunctionFieldScalar.functionFieldScalarMap (i ≫ f) := by
  exact congrArg
    (fun g : Γ(Spec (.of K), ⊤) ⟶ Y.functionField =>
      g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (openImmersionFunctionFieldIso_base i f)

/-- An actual open immersion induces an isomorphism of the canonical scalar algebras. -/
def openImmersionFunctionFieldAlgEquiv
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    X.functionField ≃ₐ[K] Y.functionField := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  refine { (openImmersionFunctionFieldIso i).commRingCatIsoToRingEquiv with
    commutes' := ?_ }
  intro c
  exact DFunLike.congr_fun (openImmersionFunctionFieldIso_scalar i f) c

variable [IsIntegral Y] [IsIntegral X]

/-- Nonempty open immersions preserve the canonical transcendence dimension.
No finite-type assumption is needed for the equality of these cardinal-to-natural values. -/
theorem schemeTranscendenceDimension_openImmersion
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of K)) :
    TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = TranscendenceDimension.schemeTranscendenceDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  exact congrArg Cardinal.toNat (openImmersionFunctionFieldAlgEquiv i f).trdeg_eq.symm

/-- In particular, restricting to any nonempty actual open subscheme preserves dimension. -/
theorem schemeTranscendenceDimension_open (f : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ f) = TranscendenceDimension.schemeTranscendenceDimension f :=
  schemeTranscendenceDimension_openImmersion U.ι f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
