package convertor;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.*;

//----www.w3.org/TR/2012/REC-owl2-primer-20121211/---
//---owlapi document----


public class Visitor implements OWLObjectVisitorEx<String>{
	private Convertor convertor;
	private String var;
	private Set<String> occ;
	private boolean flag;
	public Visitor(Convertor convertor,String var,Set<String> occ,boolean flag){

		this.convertor=convertor;
		this.var=var;
		this.occ=new HashSet<String>(occ);
		this.occ.add(var);
		this.flag=flag;
	}

	//can only generate X0 X00 X000...
	public String getUnusedVar(){
		int i=0;
		while(this.occ.contains("X"+Integer.toString(i))){
			i++;
		}
		return "X"+Integer.toString(i);
	}
	
	public String visit(OWLClassAssertionAxiom ax){
		StringBuffer s=new StringBuffer();
		//first we consider the case which there is only one simple class and individual
		//Named and unnamed? supppose the individual is named
		OWLClassExpression cl=ax.getClassExpression();
		Visitor v=new Visitor(convertor,null,this.occ,true);
		OWLIndividual ind=ax.getIndividual();
		String s_cl=cl.accept(v);
		String s_ind=convertor.getComponentsID(ind);
		s.append(s_cl+"("+s_ind+")");
		return s.toString();
	}
	
	public String visit(OWLObjectPropertyAssertionAxiom ax){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(ax.getProperty().asOWLObjectProperty());
		String s_sub=convertor.getComponentsID(ax.getSubject());
		String s_obj=convertor.getComponentsID(ax.getObject());
		s.append(s_prop+"("+s_sub+","+s_obj+")");
		return s.toString();
	}
	
	public String visit(OWLIrreflexiveObjectPropertyAxiom ax){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(ax.getProperty().asOWLObjectProperty());
		s.append("![X]:(");
		s.append("~"+s_prop+"(X,X)");
		s.append(")");
		return s.toString();
	}
	
//	public String visit(OWLObjectProperty o){
//		StringBuffer s=new StringBuffer();
//		s.toString();
//	}
//	
	public String visit(OWLClass o){
		StringBuffer s=new StringBuffer();
		String s_cl=convertor.getComponentsID(o.asOWLClass());
		if(var==null){
			s.append(s_cl);
		}else{
			s.append(s_cl+"("+var+")");
		}
		return s.toString();
	}
	
	public String visit(OWLObjectComplementOf o){
		StringBuffer s=new StringBuffer();
		OWLClassExpression cle=o.getOperand();
		Visitor v=new Visitor(convertor,var,this.occ,true);
		String s_cle=cle.accept(v);
		s.append("~("+s_cle+")");
		return s.toString();
	}
	
	public String visit(OWLSameIndividualAxiom ax){
		StringBuffer s=new StringBuffer();
		Stream<OWLIndividual> inds=ax.operands();
		List<OWLIndividual> l_inds=inds.collect(Collectors.toList());
		s.append("(");
		for(int i=0;i<l_inds.size()-1;i++){
			for(int j=i+1;j<l_inds.size();j++){
				if((i!=0)||(j!=1)){
					s.append("&");
				}
				String s_ind1=convertor.getComponentsID(l_inds.get(i));
				String s_ind2=convertor.getComponentsID(l_inds.get(j));
				s.append("("+s_ind1+"="+s_ind2+")");
			}
		}
		s.append(")");
		
		return s.toString();
	}
	
	//need to be improved
	public String visit(OWLDifferentIndividualsAxiom ax){
		StringBuffer s=new StringBuffer();
		Stream<OWLIndividual> inds=ax.operands();
		List<OWLIndividual> l_inds=inds.collect(Collectors.toList());
		s.append("(");
		for(int i=0;i<l_inds.size()-1;i++){
			for(int j=i+1;j<l_inds.size();j++){
				if((i!=0)||(j!=1)){
					s.append("&");
				}
				String s_ind1=convertor.getComponentsID(l_inds.get(i));
				String s_ind2=convertor.getComponentsID(l_inds.get(j));
				s.append("("+s_ind1+"!="+s_ind2+")");
			}
		}
		s.append(")");
		return s.toString();
	}

	public String visit(OWLTransitiveObjectPropertyAxiom ax){
		StringBuffer s=new StringBuffer();
		OWLObjectProperty prop=ax.getProperty().asOWLObjectProperty();
		String s_prop=convertor.getComponentsID(prop);
		s.append("![X,Y,Z]:("+"("+s_prop+"(X,Y)&"+s_prop+"(Y,Z))=>"+s_prop+"(X,Z))");
		return s.toString();
	}
	
	public String visit(OWLSubObjectPropertyOfAxiom ax){
		StringBuffer s=new StringBuffer();
		OWLObjectProperty sub_prop=ax.getSubProperty().asOWLObjectProperty();
		OWLObjectProperty super_prop=ax.getSuperProperty().asOWLObjectProperty();
		String s_sub_prop=convertor.getComponentsID(sub_prop);
		String s_super_prop=convertor.getComponentsID(super_prop);
		s.append("![X,Y]:("+s_sub_prop+"(X,Y)=>"+s_super_prop+"(X,Y))");
		return s.toString();
	}
	
	public String visit(OWLInverseObjectPropertiesAxiom ax){
		StringBuffer s=new StringBuffer();
		OWLObjectProperty prop1=ax.getFirstProperty().asOWLObjectProperty();
		OWLObjectProperty prop2=ax.getSecondProperty().asOWLObjectProperty();
		String s_prop1=convertor.getComponentsID(prop1);
		String s_prop2=convertor.getComponentsID(prop2);
		s.append("![X,Y]:("+s_prop1+"(X,Y)<=>"+s_prop2+"(Y,X))");
		return s.toString();
	}

	public String visit(OWLEquivalentClassesAxiom ax){
		StringBuffer s=new StringBuffer();
		Stream<OWLClassExpression> cls=ax.classExpressions();
		List<OWLClassExpression> l_cls=cls.collect(Collectors.toList());
		//remain to be tested and verified!
		if(flag){
			s.append("!["+var+"]:");
			flag=false;
		}
		if(l_cls.size()==2){
			
			Visitor v=new Visitor(convertor,var,this.occ,flag);
			String s1=l_cls.get(0).accept(v);
			String s2=l_cls.get(1).accept(v);
			s.append("("+s1+"<=>"+s2+")");
		}else{
			Collection<OWLEquivalentClassesAxiom> c_eq=ax.asPairwiseAxioms();
			//just try------
			s.append("(");
			Visitor v=new Visitor(convertor,var,this.occ,flag);
			for (Iterator<OWLEquivalentClassesAxiom> iter = c_eq.iterator(); iter.hasNext(); ) {
		          s.append(iter.next().accept(v));
		          s.append("&");
		    }
			s.deleteCharAt(s.length()-1);
			s.append(")");
		}
		return s.toString();
	}
	
	public String visit(OWLFunctionalObjectPropertyAxiom ax){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(ax.getProperty().asOWLObjectProperty());
		s.append("![X,Y,Z]:(");
		s.append("("+s_prop+"(X,Y)&"+s_prop+"(X,Z))=>(Y!=Z)");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLSubClassOfAxiom ax){
		StringBuffer s=new StringBuffer();
		Visitor v=new Visitor(convertor,var,this.occ,true);
		s.append("!["+var+"]:");
		String s_sub=ax.getSubClass().accept(v);
		String s_super=ax.getSuperClass().accept(v);
		s.append("("+s_sub+"=>"+s_super+")");
		return s.toString();
	}
	
	public String visit(OWLDisjointClassesAxiom ax){
		StringBuffer s=new StringBuffer();
		Stream<OWLClassExpression> clsE=ax.classExpressions();
		List<OWLClassExpression> l_clsE=clsE.collect(Collectors.toList());
		if(flag){
			s.append("!["+var+"]:");
			flag=false;
		}
		if(l_clsE.size()==2){

			Visitor v=new Visitor(convertor,var,this.occ,flag);
			String s1=l_clsE.get(0).accept(v);
			String s2=l_clsE.get(1).accept(v);
			s.append("~("+s1+"&"+s2+")");
		}else{
			Collection<OWLDisjointClassesAxiom> c_dj=ax.asPairwiseAxioms();
			s.append("(");
			Visitor v=new Visitor(convertor,var,this.occ,flag);
			for (Iterator<OWLDisjointClassesAxiom> iter = c_dj.iterator(); iter.hasNext(); ) {
		          s.append(iter.next().accept(v));
		          s.append("&");
		    }
			s.deleteCharAt(s.length()-1);
			s.append(")");
		}
		
		return s.toString();
	}
	
	public String visit(OWLObjectIntersectionOf o){
		StringBuffer s=new StringBuffer();
		Stream<OWLClassExpression> cls=o.conjunctSet();
		List<OWLClassExpression> l_cls=cls.collect(Collectors.toList());
		s.append("(");
		for(int i=0;i<l_cls.size();i++){
			Visitor v=new Visitor(convertor,var,this.occ,true);
			String cj=l_cls.get(i).accept(v);
			s.append(cj);
			if(i!=l_cls.size()-1){
				s.append("&");
			}
		}
		s.append(")");
		return s.toString();
		
	}
	
	public String visit(OWLObjectUnionOf o){
		StringBuffer s=new StringBuffer();
		Stream<OWLClassExpression> cls=o.disjunctSet();
		List<OWLClassExpression> l_cls=cls.collect(Collectors.toList());
		s.append("(");
		for(int i=0;i<l_cls.size();i++){
			Visitor v=new Visitor(convertor,var,this.occ,true);
			String cj=l_cls.get(i).accept(v);
			s.append(cj);
			if(i!=l_cls.size()-1){
				s.append("|");
			}
		}
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectSomeValuesFrom o){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(o.getProperty().asOWLObjectProperty());
		String newVar=getUnusedVar();
		Visitor v=new Visitor(convertor,newVar,this.occ,true);
		String filler=o.getFiller().accept(v);
		s.append("(");
		s.append("?["+newVar+"]:(");
		s.append(s_prop+"("+var+","+newVar+")&("+filler+")");
		s.append(")");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectAllValuesFrom o){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(o.getProperty().asOWLObjectProperty());
		String newVar=getUnusedVar();
		Visitor v=new Visitor(convertor,newVar,this.occ,true);
		String filler=o.getFiller().accept(v);
		s.append("(");
		s.append("!["+newVar+"]:(");
		s.append(s_prop+"("+var+","+newVar+")=>("+filler+")");
		s.append(")");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectOneOf o){
		StringBuffer s=new StringBuffer();
		Stream<OWLIndividual> ins=o.individuals();
		List<OWLIndividual> l_ins=ins.collect(Collectors.toList());
		s.append("(");
		for(int i=0;i<l_ins.size();i++){
			s.append(var+"="+convertor.getComponentsID(l_ins.get(i)));
			if(i!=l_ins.size()-1){
				s.append("|");
			}
		}
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLAsymmetricObjectPropertyAxiom ax){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(ax.getProperty().asOWLObjectProperty());
		s.append("![X,Y]:(");
		s.append("("+s_prop+"(X,Y)=>~"+s_prop+"(Y,X))");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLInverseFunctionalObjectPropertyAxiom ax){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(ax.getProperty().asOWLObjectProperty());
		s.append("![X,Y,Z]:(");
		s.append("("+s_prop+"(X,Z)&"+s_prop+"(Y,Z))=>(X=Y)");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectHasValue o){
		StringBuffer s=new StringBuffer();
		OWLClassExpression svf=o.asSomeValuesFrom();
		Visitor v=new Visitor(convertor,var,this.occ,true);
		s.append(svf.accept(v));
		return s.toString();
	}
	
	public String visit(OWLObjectMinCardinality o){
		StringBuffer s=new StringBuffer();
		int card=o.getCardinality();
		s.append("?[");
		for(int i=1;i<=card;i++){
			s.append(var+Integer.toString(i));
			if(i!=card){
				s.append(",");
			}
		}
		s.append("]:");
		s.append("(");
		for(int i=1;i<=card-1;i++){
			for(int j=i+1;j<=card;j++){
				if((i!=1)||(j!=2)){
					s.append("&");
				}
				s.append("("+var+Integer.toString(i)+"!="+var+Integer.toString(j)+")");
			}
		}
		if(card!=1){
			s.append("&");
		}
		for(int i=1;i<=card;i++){
			String s_prop=convertor.getComponentsID(o.getProperty().asOWLObjectProperty());
			Visitor v=new Visitor(convertor,var+Integer.toString(i),this.occ,true);
			String s_cls=o.getFiller().accept(v);
			s.append("("+s_prop+"("+var+","+var+Integer.toString(i)+")&"+s_cls+")");
			if(i!=card){
				s.append("&");
			}
		}
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectMaxCardinality o){
		StringBuffer s=new StringBuffer();
		int card=o.getCardinality()+1;
		s.append("~(?[");
		for(int i=1;i<=card;i++){
			s.append(var+Integer.toString(i));
			if(i!=card){
				s.append(",");
			}
		}
		s.append("]:");
		s.append("(");
		for(int i=1;i<=card-1;i++){
			for(int j=i+1;j<=card;j++){
				if((i!=1)||(j!=2)){
					s.append("&");
				}
				s.append("("+var+Integer.toString(i)+"!="+var+Integer.toString(j)+")");
			}
		}
		if(card!=1){
			s.append("&");
		}
		for(int i=1;i<=card;i++){
			String s_prop=convertor.getComponentsID(o.getProperty().asOWLObjectProperty());
			Visitor v=new Visitor(convertor,var+Integer.toString(i),this.occ,true);
			String s_cls=o.getFiller().accept(v);
			s.append("("+s_prop+"("+var+","+var+Integer.toString(i)+")&"+s_cls+")");
			if(i!=card){
				s.append("&");
			}
		}
		s.append(")");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectPropertyRangeAxiom o){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(o.getProperty().asOWLObjectProperty());
		String newVar=getUnusedVar();
		s.append("!["+var+","+newVar+"]:");
		Visitor v=new Visitor(convertor,newVar,this.occ,true);
		String s_cls=o.getRange().accept(v);
		s.append("(");
		s.append(s_prop+"("+var+","+newVar+")=>"+s_cls);
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectPropertyDomainAxiom o){
		StringBuffer s=new StringBuffer();
		String s_prop=convertor.getComponentsID(o.getProperty().asOWLObjectProperty());
		String newVar=getUnusedVar();
		s.append("!["+var+"]:(");
		s.append("?["+newVar+"]:(");
		Visitor v=new Visitor(convertor,var,this.occ,true);
		String s_cls=o.getDomain().accept(v);
		s.append(s_prop+"("+var+","+newVar+")=>"+s_cls);
		s.append(")");
		s.append(")");
		return s.toString();
	}
	
	public String visit(OWLObjectExactCardinality o){
		StringBuffer s=new StringBuffer();
		OWLClassExpression cle=o.asIntersectionOfMinMax();
		String newVar=getUnusedVar();
		Visitor v=new Visitor(convertor,newVar,this.occ,true);
		s.append("(");
		s.append(cle.accept(v));
		s.append(")");
		return  s.toString();
	}
	
}
