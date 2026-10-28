import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidityEq

/-! # Line Rigidification At -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification

noncomputable section

/-! Prescribing the fiber of a line-bundle isomorphism when global functions are unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def endPullbackEquiv (f : X ⟶ Y) [IsIso f.appTop] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    End L.sheaf ≃+* End (L.pullback f).sheaf :=
  (LineEndRing.Construction.LineScalars.endRingEquiv L).symm.trans
    ((asIso f.appTop).commRingCatIsoToRingEquiv.trans (LineEndRing.Construction.LineScalars.endRingEquiv (L.pullback f)))

theorem endPullbackEquiv_apply (f : X ⟶ Y) [IsIso f.appTop] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (a : End L.sheaf) :
    endPullbackEquiv f L a = (Scheme.Modules.pullback f).map a := by
  obtain ⟨r, rfl⟩ := LineEndRing.Construction.LineScalars.scalar_surjective L a
  change (LineEndRing.Construction.LineScalars.endRingEquiv (L.pullback f))
    (f.appTop ((LineEndRing.Construction.LineScalars.endRingEquiv L).symm ((LineEndRing.Construction.LineScalars.endRingEquiv L) r))) = _
  rw [RingEquiv.symm_apply_apply]
  exact (ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar f L.sheaf r).symm

theorem exists_iso (f : X ⟶ Y) [IsIso f.appTop] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : L.sheaf ≅ M.sheaf)
    (φ : (L.pullback f).sheaf ≅ (M.pullback f).sheaf) :
    ∃ e' : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback f).mapIso e' = φ := by
  change (Scheme.Modules.pullback f).obj L.sheaf ≅ (Scheme.Modules.pullback f).obj M.sheaf at φ
  let d : End ((Scheme.Modules.pullback f).obj L.sheaf) := φ.hom ≫ (Scheme.Modules.pullback f).map e.inv
  have : IsIso d := by dsimp [d]; infer_instance
  let d₀ := (endPullbackEquiv f L).symm d
  have hd : (Scheme.Modules.pullback f).map d₀ = d :=
    (endPullbackEquiv_apply f L d₀).symm.trans ((endPullbackEquiv f L).apply_symm_apply d)
  have hunit : IsUnit d₀ := ((isUnit_iff_isIso d).mpr inferInstance).map
    (endPullbackEquiv f L).symm.toMonoidHom
  have : IsIso d₀ := (isUnit_iff_isIso d₀).mp hunit
  refine ⟨asIso d₀ ≪≫ e, ?_⟩
  apply Iso.ext
  change (Scheme.Modules.pullback f).map (d₀ ≫ e.hom) = φ.hom
  rw [Functor.map_comp, hd]
  dsimp only [d]
  rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id,
    (Scheme.Modules.pullback f).map_id, Category.comp_id]

theorem iso_unique (f : X ⟶ Y) [IsIso f.appTop] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e e' : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback f).mapIso e = (Scheme.Modules.pullback f).mapIso e') : e = e' := by
  apply Iso.ext
  apply (cancel_mono e.inv).mp
  apply (endPullbackEquiv f L).injective
  rw [endPullbackEquiv_apply, endPullbackEquiv_apply, Functor.map_comp, Functor.map_comp]
  exact congrArg (fun a => a.hom ≫ (Scheme.Modules.pullback f).map e.inv) h

theorem existsUnique_iso (f : X ⟶ Y) [IsIso f.appTop] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : L.sheaf ≅ M.sheaf)
    (φ : (L.pullback f).sheaf ≅ (M.pullback f).sheaf) :
    ∃! e' : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback f).mapIso e' = φ := by
  obtain ⟨e', he'⟩ := exists_iso f L M e φ
  exact ⟨e', he', fun e'' he'' => iso_unique f L M e'' e' (he''.trans he'.symm)⟩

/-- An existing isomorphism of line bundles on a proper connected reduced
scheme can be uniquely normalized to any prescribed isomorphism at a rational point. -/
theorem existsUnique_iso_at_rational_point {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [IsProper A.hom] [ConnectedSpace A.left] [IsReduced A.left]
    (p : Spec (.of K) ⟶ A.left) (hp : p ≫ A.hom = 𝟙 _)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (e : L.sheaf ≅ M.sheaf)
    (φ : (L.pullback p).sheaf ≅ (M.pullback p).sheaf) :
    ∃! e' : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback p).mapIso e' = φ := by
  have : IsIso A.hom.appTop := ProperFunctionsEq.Construction.ProperFunctions.isIso_appTop_of_section A p hp
  have : IsIso (A.hom.appTop ≫ p.appTop) := by
    rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
    infer_instance
  have : IsIso p.appTop := (isIso_comp_left_iff _ _).mp this
  exact existsUnique_iso p L M e φ

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification
