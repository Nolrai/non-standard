// This file is part of Golly.
// See docs/License.html for the copyright notice.

#include <math.h>
#include <time.h>

#include <iostream>
#include <set>
#include <fstream>
#include <vector>
#include <map>
#include <sstream>
#include <algorithm>
using namespace std;

/*

Makes a rule-table for your transition function.

To compile:
g++ -O5 -o make-ruletable make-ruletable.cpp
or in Microsoft Visual Studio, add to an empty CLR project.

To use:
1) fill slowcalc with your own transition function.
2) set the parameters in main() at the bottom.
3) execute the program from the command line (no options taken)

For a 32-state 5-neighbourhood rule it took 16mins on a 2.2GHz machine.
For a 4-state 9-neighbourhood rule it took 4s.

The merging is very simple - if a transition is compatible with the first rule, 
then merge the transition into the rule. If not, try the next rule. If there are
no more rules, add a new rule containing just the transition. 

=== Worked example: ===
Transitions: 
1,0,0->3
1,2,0->3
2,0,0->3
2,2,0->1
Start. First transition taken as first rule:
rule 1: 1,0,0->3
Next transition - is it compatible with rule 1? 
i.e. is 1,[0,2],0->3 valid for all permutations? Yes.
rule 1 now: 1,[0,2],0->3
Next transition - is it compatible with rule 1?
i.e. is [1,2],[0,2],0->3 valid for all permutations?
no - because 2,2,0 ->1, not ->3. so add the transition as a new rule:
rule 1 still: 1,[0,2],0 -> 3
rule 2 now : 2,0,0->3
Next transition - is it compatible with rule 1? no - output is different.
Is it compatible with rule 2? no - output is different.
Final output:
1,[0,2],0 -> 3
2,0,0 -> 3
2,2,0 -> 1
Written with variables:
var a={0,2}
1,a,0,3
2,0,0,3
2,2,0,1
===============

In the function produce_rule_table, the state space is exhaustively traversed.
If your transition function consists of transition rules already then you can
optimise by running through the transitions instead. You might also want to
turn off the optimisation in rule::can_merge, to see if it gives you better
compression.

Also note: I feel sure there are better ways to compress rule tables than this...

Contact: Tim Hutton <tim.hutton@gmail.com>

*/

// some typedefs and compile-time constants
// typedef unsigned short state;
enum TSymm { none, rotate4, rotate8, reflect, rotate4reflect, rotate8reflect };
static const string symmetry_strings[] = {"none","rotate4","rotate8","reflect","rotate4reflect","rotate8reflect"};

typedef enum state {Empty, LowWasLow, LowWasHigh, HighWasLow, HighWasHigh, PastEnd};
typedef enum LowHigh {Low, High};

// prefix
state& operator++(state& orig)
{
  orig = static_cast<state>(orig + 1); // static_cast required because enum + int -> int
  // dont wrap so we can test for PastEnd
  return orig;
}

// postfix
state operator++(state& orig, int)
{
  state rVal = orig;
  ++orig;
  return rVal;
}

// fill in this function with your desired transition rules
// (for von Neumann neighbourhoods, just ignore the nw,se,sw,ne inputs)
state slowcalc(state nw,state n,state ne,state w,state c,state e,state sw,state s,state se)
{

   // flowgate_simp
   state ret;
   if (Empty == c) {
      ret = Empty;
   }
   else {
      LowHigh c_now = (HighWasHigh == c | HighWasLow == c) ? High : Low;
      LowHigh c_past = (LowWasHigh == c | HighWasHigh == c) ? High : Low;
      state now[8] = {nw, n, ne, w, e, sw, s, se};
      int count = 0;
      for (int i = 0; i < 8; i++){
         if (HighWasHigh == now[i] | HighWasLow == now[i]) {
            count++;
         }
      }
      LowHigh c_new = c_past;
      switch(count) {
         case 1:
         case 2:
            c_new = (High == c_new) ? Low : High;
            break;
         default: break; //do nothing
      }
      if (High == c_new) {
         if (High == c_now) {
            ret = HighWasHigh;
         } else {
            ret = HighWasLow;
         }
      } else {
         if (High == c_now) {
            ret = LowWasHigh;
         } else {
            ret = LowWasLow;
         }
      }
   }
   return ret;
}

vector<state> rotate_inputs(const vector<state>& inputs,int rot)
{
   vector<state> rotinp(inputs);
   rotate_copy(inputs.begin()+1,inputs.begin()+1+rot,inputs.end(),rotinp.begin()+1);
   return rotinp;
}

vector<state> reflect_inputs(const vector<state>& inputs,int neighbourhood_size)
{
   vector<state> refinp(inputs);
   if(neighbourhood_size==5) // CNESW
   {
      refinp[2]=inputs[4]; // swap E and W
      refinp[4]=inputs[2];
   }
   else // neighbourhood_size==9 (C,N,NE,E,SE,S,SW,W,NW)
   {
      refinp[2]=inputs[8];
      refinp[8]=inputs[2];
      refinp[3]=inputs[7];
      refinp[7]=inputs[3];
      refinp[4]=inputs[6];
      refinp[6]=inputs[4]; // swap all E and W
   }
   return refinp;
}

// simple rule structure, e.g. 1,2,[4,5],8,2 -> 0
class rule { 

public:
   set<state> inputs[9]; // c,n,ne,e,se,s,sw,w,nw  or  c,n,e,s,w
   state ns; // new state

   int n_inputs; // 5: von Neumann; 9: Moore
   TSymm symm;

public:
   // constructors
   rule(const rule& r) : ns(r.ns),n_inputs(r.n_inputs),symm(r.symm)
   {
      for(int i=0;i<n_inputs;i++)
         inputs[i]=r.inputs[i];
   }
   rule& operator=(const rule& r) 
   {
      n_inputs=r.n_inputs;
      symm = r.symm;
      ns = r.ns;
      for(int i=0;i<n_inputs;i++)
         inputs[i]=r.inputs[i];
      return *this;
   }
   rule(const vector<state>& inputs,int n_inputs,state ns1,TSymm symm1) 
      : ns(ns1),n_inputs(n_inputs),symm(symm1)
   {
      merge(inputs);
   }

   // if we merge the rule and the supplied transition, will the rule remain true for all cases?
   bool can_merge(const vector<state>& test_inputs,state ns1) const
   {
      if(ns1!=ns) return false; // can't merge if the outputs are different

      // If you are running through your own transitions, or for small state spaces,
      // you might want to turn off this optimisation, to get better compression. 
      // On JvN29 it doesn't make any difference but on Nobili32 it does.
      const bool forbid_multiple_input_differences = true;

      if(forbid_multiple_input_differences)
      {
         // optimisation: we skip this rule if more than 2 entries are different, we 
         // assume we will have considered the relevant one-change rules before this. 
         int n_different=0;
         for(int i=0;i<n_inputs;i++)
            if(inputs[i].find(test_inputs[i])==inputs[i].end())
               if(++n_different>1)
                  return false;
         // just check the new permutations
         for(int i=0;i<n_inputs;i++)
         {
            if(inputs[i].find(test_inputs[i])==inputs[i].end())
            {
               rule r1(*this);
               r1.inputs[i].clear(); // (since we don't need to re-test all the other permutations) 
               r1.inputs[i].insert(test_inputs[i]);
               if(!r1.all_true()) return false;
            }
         }
      }
      else
      {
         // need to check all combinations - this can be very slow for large state spaces
         for(int i=0;i<n_inputs;i++)
         {
            if(inputs[i].find(test_inputs[i])==inputs[i].end())
            {
               rule r1(*this);
               r1.merge(test_inputs); // this is what makes it slow, we may introduce many new permutations
               r1.inputs[i].clear(); // (since we don't need to re-test all the old permutations) 
               r1.inputs[i].insert(test_inputs[i]);
               if(!r1.all_true()) return false;
            }
         }
      }
      return true;
   }
   // merge the inputs with this rule
   void merge(const vector<state>& new_inputs)
   {
      for(int i=0;i<n_inputs;i++)
         inputs[i].insert(new_inputs[i]); // may already exist, set ignores if so
   }

   // is this set of inputs a match for the rule, for the given symmetry?
   bool matches(const vector<state>& test_inputs) const
   {
      int n_rotations,rotation_skip;
      bool do_reflect;
      switch(symm)
      {
         default:
         case none: n_rotations=1; rotation_skip=1; do_reflect=false; break;
         case rotate4:
            if(n_inputs==5)
            {
               n_rotations=4; rotation_skip=1; do_reflect=false;
            }
            else
            {
               n_rotations=4; rotation_skip=2; do_reflect=false;
            }
            break;
         case rotate8: n_rotations=8; rotation_skip=1; do_reflect=false; break;
         case reflect: n_rotations=1; rotation_skip=1; do_reflect=true; break;
         case rotate4reflect: 
            if(n_inputs==5)
            {
               n_rotations=4; rotation_skip=1; do_reflect=true;
            }
            else
            {
               n_rotations=4; rotation_skip=2; do_reflect=true;
            }
            break;
         case rotate8reflect: n_rotations=8; rotation_skip=1; do_reflect=true; break;
      }
      for(int iRot=0;iRot<n_rotations;iRot++)
      {
         if(nosymm_matches(rotate_inputs(test_inputs,iRot*rotation_skip)))
            return true;
         if(do_reflect && nosymm_matches(reflect_inputs(rotate_inputs(test_inputs,iRot*rotation_skip),n_inputs)))
            return true;
      }
      return false; // no match found
   }

protected:

   // ignoring symmetry, does this set of inputs match the rule?
   bool nosymm_matches(const vector<state>& test_inputs) const
   {
      for(int i=0;i<n_inputs;i++)
         if(inputs[i].find(test_inputs[i])==inputs[i].end())
            return false;
      return true;
   }

   // is the rule true in all permutations?
   bool all_true() const
   {
      set<state>::const_iterator c_it,n_it,ne_it,e_it,se_it,s_it,sw_it,w_it,nw_it;
      if(n_inputs==9)
      {
         for(c_it = inputs[0].begin();c_it!=inputs[0].end();c_it++)
            for(n_it = inputs[1].begin();n_it!=inputs[1].end();n_it++)
               for(ne_it = inputs[2].begin();ne_it!=inputs[2].end();ne_it++)
                  for(e_it = inputs[3].begin();e_it!=inputs[3].end();e_it++)
                     for(se_it = inputs[4].begin();se_it!=inputs[4].end();se_it++)
                        for(s_it = inputs[5].begin();s_it!=inputs[5].end();s_it++)
                           for(sw_it = inputs[6].begin();sw_it!=inputs[6].end();sw_it++)
                              for(w_it = inputs[7].begin();w_it!=inputs[7].end();w_it++)
                                 for(nw_it = inputs[8].begin();nw_it!=inputs[8].end();nw_it++)
                                    if(slowcalc(*nw_it,*n_it,*ne_it,*w_it,*c_it,*e_it,*sw_it,*s_it,*se_it)!=ns)
                                       return false;
      }
      else
      {
         for(c_it = inputs[0].begin();c_it!=inputs[0].end();c_it++)
            for(n_it = inputs[1].begin();n_it!=inputs[1].end();n_it++)
               for(e_it = inputs[2].begin();e_it!=inputs[2].end();e_it++)
                  for(s_it = inputs[3].begin();s_it!=inputs[3].end();s_it++)
                     for(w_it = inputs[4].begin();w_it!=inputs[4].end();w_it++)
                        if(slowcalc(Empty,*n_it,Empty,*w_it,*c_it,*e_it,Empty,*s_it,Empty)!=ns)
                           return false;
      }
      return true;
   }
};

// makes a unique variable name for a given value
string get_variable_name(unsigned int iVar)
{
   const char VARS[52]={'a','b','c','d','e','f','g','h','i','j',
      'k','l','m','n','o','p','q','r','s','t','u','v','w','x',
      'y','z','A','B','C','D','E','F','G','H','I','J','K','L',
      'M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z'};
   ostringstream oss;
   if(iVar<52)
      oss << VARS[iVar];
   else if(iVar<52*52)
      oss << VARS[(iVar-(iVar%52))/52 - 1] << VARS[iVar%52];
   else
      oss << "!"; // we have a 52*52 limit ("should be enough for anyone")
   return oss.str();
}

void print_rules(const vector<rule>& rules,ostream& out)
{
   // first collect all variables (makes reading easier)
   map< string , set<state> > vars;
   ostringstream rules_out;
   for(vector<rule>::const_iterator r_it=rules.begin();r_it!=rules.end();r_it++)
   {
      vector<string> variables_used;
      for(int i=0;i<r_it->n_inputs;i++)
      {
         // if more than one state for this input, we need a variable 
         if(r_it->inputs[i].size()>1)
         {
            string var;
            // is there a variable that matches these inputs, and that we haven't used?
            bool found_unused_var=false;
            for(map<string, set<state> >::const_iterator v_it=vars.begin();v_it!=vars.end();v_it++)
            {
               if(v_it->second==r_it->inputs[i] && find(variables_used.begin(),variables_used.end(),v_it->first)==variables_used.end())
               {
                  found_unused_var = true;
                  var = v_it->first;
                  break;
               }
            }
            if(!found_unused_var)
            {
               // we need to make a new one for this set of inputs
               var = get_variable_name(vars.size());
               // add it to the list of made variables
               vars[var] = r_it->inputs[i];
               // print it
               out << "var " << var << "={";
               set<state>::const_iterator it=r_it->inputs[i].begin();
               while(true)
               {
                  out << (int)*it;
                  it++;
                  if(it!=r_it->inputs[i].end()) out << ",";
                  else break;
               }
               out << "}\n";
            }
            // add the variable to the list of used ones
            variables_used.push_back(var);
            rules_out << var << ",";
         }
         else
         {
            // just a state, output it
            rules_out << (int)*r_it->inputs[i].begin() << ",";
         }
      }
      rules_out << (int)r_it->ns << endl;
   }
   out << rules_out.str();
}

void produce_rule_table(vector<rule>& rules,int nhood_size,TSymm symm,bool remove_stasis)
{
   int n_rotations,rotation_skip;
   bool do_reflect;
   switch(symm)
   {
      default:
      case none: n_rotations=1; rotation_skip=1; do_reflect=false; break;
      case rotate4:
         if(nhood_size==5)
         {
            n_rotations=4; rotation_skip=1; do_reflect=false;
         }
         else
         {
            n_rotations=4; rotation_skip=2; do_reflect=false;
         }
         break;
      case rotate8: n_rotations=8; rotation_skip=1; do_reflect=false; break;
      case reflect: n_rotations=1; rotation_skip=1; do_reflect=true; break;
      case rotate4reflect: 
         if(nhood_size==5)
         {
            n_rotations=4; rotation_skip=1; do_reflect=true;
         }
         else
         {
            n_rotations=4; rotation_skip=2; do_reflect=true;
         }
         break;
      case rotate8reflect: n_rotations=8; rotation_skip=1; do_reflect=true; break;
   }

   state c,n,ne,nw,sw,s,se,e,w,ns;
   vector<rule>::iterator it;
   bool merged;
   for(c=Empty;c<PastEnd;c++)
   {
      cout << "\nProcessing for c=" << (int)c << ", " << rules.size() << " rules so far." << endl;

      if(nhood_size==9)
      {
         vector<state> inputs(9);
         inputs[0]=c;
         for(n=Empty;n<PastEnd;n++)
         {
            cout << ".";
            cout.flush();
            inputs[1]=n;
            for(ne=Empty;ne<PastEnd;ne++)
            {
               inputs[2]=ne;
               for(e=Empty;e<PastEnd;e++)
               {
                  inputs[3]=e;
                  for(se=Empty;se<PastEnd;se++)
                  {
                     inputs[4]=se;
                     for(s=Empty;s<PastEnd;s++)
                     {
                        inputs[5]=s;
                        for(sw=Empty;sw<PastEnd;sw++)
                        {
                           inputs[6]=sw;
                           for(w=Empty;w<PastEnd;w++)
                           {
                              inputs[7]=w;
                              for(nw=Empty;nw<PastEnd;nw++)
                              {
                                 ns = slowcalc(nw,n,ne,w,c,e,sw,s,se);
                                 if(remove_stasis && ns == c)
                                    continue; // we can ignore stasis transitions
                                 // can we merge this transition with any existing rule?
                                 inputs[8]=nw;
                                 merged = false;
                                 for(it=rules.begin();!merged && it!=rules.end();it++)
                                 {
                                    rule &r = *it;
                                    for(int iRot=0;!merged && iRot<n_rotations;iRot++)
                                    {
                                       if(r.can_merge(rotate_inputs(inputs,iRot*rotation_skip),ns))
                                       {
                                          r.merge(rotate_inputs(inputs,iRot*rotation_skip));
                                          merged = true;
                                       }
                                       else if(do_reflect && r.can_merge(reflect_inputs(rotate_inputs(inputs,iRot*rotation_skip),nhood_size),ns))
                                       {
                                          r.merge(reflect_inputs(rotate_inputs(inputs,iRot*rotation_skip),nhood_size));
                                          merged = true;
                                       }
                                    }
                                 }
                                 if(!merged)
                                 {
                                    // need to make a new rule starting with this transition
                                    rule r(inputs,nhood_size,ns,symm);
                                    rules.push_back(r);
                                 }
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      }
      else // nhood_size==5
      {
         vector<state> inputs(5);
         inputs[0]=c;
         for(n=Empty;n<PastEnd;n++)
         {
            cout << ".";
            cout.flush();
            inputs[1]=n;
            for(e=Empty;e<PastEnd;e++)
            {
               inputs[2]=e;
               for(s=Empty;s<PastEnd;s++)
               {
                  inputs[3]=s;
                  for(w=Empty;w<PastEnd;w++)
                  {
                     ns = slowcalc(Empty,n,Empty,w,c,e,Empty,s,Empty);
                     if(remove_stasis && ns == c)
                        continue; // we can ignore stasis transitions

                     // can we merge this transition with any existing rule?
                     inputs[4]=w;
                     merged = false;
                     for(it=rules.begin();!merged && it!=rules.end();it++)
                     {
                        rule &r = *it;
                        for(int iRot=0;!merged && iRot<n_rotations;iRot++)
                        {
                           if(r.can_merge(rotate_inputs(inputs,iRot*rotation_skip),ns))
                           {
                              r.merge(rotate_inputs(inputs,iRot*rotation_skip));
                              merged = true;
                           }
                           else if(do_reflect && r.can_merge(reflect_inputs(rotate_inputs(inputs,iRot*rotation_skip),nhood_size),ns))
                           {
                              r.merge(reflect_inputs(rotate_inputs(inputs,iRot*rotation_skip),nhood_size));
                              merged = true;
                           }
                        }
                     }
                     if(!merged)
                     {
                        // need to make a new rule starting with this transition
                        rule r(inputs,nhood_size,ns,symm);
                        rules.push_back(r);
                     }
                  }
               }
            }
         }
      }
   }
}

// here we use the computed rule table as a replacement slowcalc, for checking correctness
state new_slowcalc(const vector<rule>& rules, const vector<state>& inputs) 
{
   for(vector<rule>::const_iterator it=rules.begin();it!=rules.end();it++)
      if(it->matches(inputs))
         return it->ns;
    return inputs[0]; // default: no change
}

bool is_correct(const vector<rule>&rules, int neighbourhood_size)
{
   // exhaustive check
   state c,n,ne,nw,sw,s,se,e,w;
   if(neighbourhood_size==9)
   {
      vector<state> inputs(9);
      for(c=Empty;c<PastEnd;c++)
      {
         inputs[0]=c;
         for(n=Empty;n<PastEnd;n++)
         {
            inputs[1]=n;
            for(ne=Empty;ne<PastEnd;ne++)
            {
               inputs[2]=ne;
               for(e=Empty;e<PastEnd;e++)
               {
                  inputs[3]=e;
                  for(se=Empty;se<PastEnd;se++)
                  {
                     inputs[4]=se;
                     for(s=Empty;s<PastEnd;s++)
                     {
                        inputs[5]=s;
                        for(sw=Empty;sw<PastEnd;sw++)
                        {
                           inputs[6]=sw;
                           for(w=Empty;w<PastEnd;w++)
                           {
                              inputs[7]=w;
                              for(nw=Empty;nw<PastEnd;nw++)
                              {
                                 inputs[8]=nw;
                                 if(new_slowcalc(rules,inputs) 
                                    != slowcalc(nw,n,ne,w,c,e,sw,s,se))
                                       return false;
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      }
   }
   else
   {
      vector<state> inputs(5);
      for(c=Empty;c<PastEnd;c++)
      {
         inputs[0]=c;
         for(n=Empty;n<PastEnd;n++)
         {
            inputs[1]=n;
            for(e=Empty;e<PastEnd;e++)
            {
               inputs[2]=e;
               for(s=Empty;s<PastEnd;s++)
               {
                  inputs[3]=s;
                  for(w=Empty;w<PastEnd;w++)
                  {
                     inputs[4]=w;
                     if(new_slowcalc(rules,inputs) 
                        != slowcalc(Empty,n,Empty,w,c,e,Empty,s,Empty))
                        return false;
                  }
               }
            }
         }
      }
   }
   return true;
}

int main()
{
   // parameters for use:
   const TSymm symmetry = rotate8reflect;
   const int nhood_size = 9;
   const string output_filename = "flowgate2.table";
   const bool remove_stasis_transitions = true;

   vector<rule> rules;
   time_t t1,t2;
   time(&t1);
   produce_rule_table(rules,nhood_size,symmetry,remove_stasis_transitions);
   time(&t2);
   int n_secs = (int)difftime(t2,t1);
   cout << "\nProcessing took: " << n_secs << " seconds." << endl;

   {
      ofstream out(output_filename.c_str());
      out << "# rules: " << rules.size() << "\n#";
      out << "\n# Golly rule-table format.\n# Each rule: C,";
      if(nhood_size==5)
         out << "N,E,S,W";
      else
         out << "N,NE,E,SE,S,SW,W,NW";
      out << ",C'";
      out << "\n# N.B. Where the same variable appears multiple times in a transition,\n# it takes the same value each time.\n#";
      if(remove_stasis_transitions)
         out << "\n# Default for transitions not listed: no change\n#";
      else
         out << "\n# All transitions should be included below, including no-change ones.\n#";
      out << "\nn_states:" << PastEnd;
      out << "\nneighborhood:" << ((nhood_size==5)?("vonNeumann"):("Moore"));
      out << "\nsymmetries:" << symmetry_strings[symmetry] << "\n";
      print_rules(rules,out);
   }
   cout << rules.size() << " rules written." << endl;

   // optional: run through the entire state space, checking that new_slowcalc matches slowcalc
   cout << "Verifying is correct (can abort if you're confident)...";
   cout.flush();
   if(is_correct(rules,nhood_size))
      cout << "yes." << endl;
   else
      cout << "no! Either there's a bug in the code, or the transition function does not have the symmetry you selected." << endl;
}
