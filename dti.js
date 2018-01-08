/*
 * Copyright 2014 Samsung Information Systems America, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Author: Nico Naus
// Currently not supported: prototype extensions, array inner typing, coverage recording

// do not remove the following comment
// JALANGI DO NOT INSTRUMENT


(function (sandbox) {
    function MyAnalysis () {
        var iidToLocation = sandbox.iidToLocation;
        var getGlobalIID = sandbox.getGlobalIID;
            
        var observations = [];
        var trustedObservations = [];
        var observedAnnotations = [];

        var count = 1;
        var currentFrame = ["global"];

        //GLOBAL ANALYSIS SETTINGS
        
        var debugCollect = false;

        var timeExecution = true;

        var printWarnings = true;
        var printErrors = true;
        var printTypes = true;

        var condenseReports = true;

        var filterNativeFunctions = true;

        var pruneNullInc = true; //ignore inconsistencies with NULL
        var pruneTypeDif = 2; //ignore inconsistencies with bigger type difference then this
        var pruneTypeCount = 5; //ignore inconsistencies with more types than this value

        //END OF ANALYSIS SETTINGS
        if(timeExecution){console.time("total");}
        //Jalangi2 API functions:


        //TAG ALL OBJECTS

        this.invokeFunPre = function(iid, f, base, args, isConstructor, isMethod){
            
            if(f && f.name){annotate(base,f.name);}
            else {annotate(base);}
            return {f:f,base:base,args:args,skip:false};
        };

        this.functionEnter = function (iid, f, dis, args){currentFrame.push(getAnnotation(f));};

        this.getFieldPre = function(iid, base, offset, isComputed, isOpAssign, isMethodCall){
            if(base && !getAnnotation(base)) {base=annotate(base);}
            return {base:base,offset:offset,skip:false};
        };

        this.putFieldPre = function(iid, base, offset, val, isComputed, isOpAssign){
            if(!base.shadow) {base=annotate(base);}
            return {base:base,offset:offset,val:val,skip:false};
        };


        this.functionExit = function(iid, returnVal, wrappedExceptionVal){
            if(currentFrame.length>1){currentFrame.pop();} else {console.log("no frame to pop :(");}
            if(returnVal && ((typeof base === "object")||(typeof base === "function")) && !getAnnotation(returnVal)) {returnVal=annotate(returnVal);}
            return {returnVal:returnVal,wrappedExceptionVal:wrappedExceptionVal,isBacktrack:false};
        };
        

        //COLLECT TYPE INFORMATION

        this.invokeFun = function(iid, f, base, args, result, isConstructor, isMethod){
            if(filterNativeFunctions && isNative(f)){return;}
            //deal with constructors

            if (isConstructor){annotate(result);}

            for (var arg in args){
                if(typeof arg == 'string'){collect("function " + getAnnotation(f), "arg" + arg, toType(args[arg],getGlobalIID(iid)));}
             }
            collect("function " + getAnnotation(f) , "return" , toType(result,getGlobalIID(iid)));
            if(result && ((typeof base === "object")||(typeof base === "function")) && !getAnnotation(result)) {result=annotate(result);}   
        };

        this.getField = function(iid, base, offset, val, isComputed, isOpAssign, isMethodCall){

            if (val!== undefined && base.constructor.name !== "Array") {

                var provider = base;
                while (provider !== null && provider !== undefined && typeof provider === "object" && !Object.prototype.hasOwnProperty.call(provider,offset)){
                    provider = Object.getPrototypeOf(provider);
                }
                //console.log(provider);
                if(typeof base === "object") {collect("object " + getAnnotation(provider), offset, toType(val,getGlobalIID(iid)));}
                else if(typeof base === "function") {collect("function " + getAnnotation(provider), offset, toType(val,getGlobalIID(iid)));}
            }
        };

        this.putField = function(iid, base, offset, val, isComputed, isOpAssign){
        
            if (val!== undefined &&
                ((typeof base === "object")||(typeof base === "function")) &&
                base.constructor.name !== "Array") {
                        collect(toType(base), offset , toType(val,getGlobalIID(iid)) );
                    }
        };

        //CONTAINS A BUG: does lot look up what frame the current variable belongs to. ??????? does it?
        this.read = function(iid,name,val,isGlobal,isScriptLocal){
            if(name=='this') {return;}

            var base = "frame " + currentFrame[currentFrame.length-1];
            if(isGlobal||isScriptLocal){base = "frame global";}
            
            if(!val) {collect(base,name,toType(val,sandbox.getGlobalIID(iid)));return;}
            if(getAnnotation(val)){collect(base,name,toType(val,getGlobalIID(iid)));}
            else if(val.constructor.name == "object") {collect(annotate(base),name,toType(val,getGlobalIID(iid)));}
                 else {collect(base,name,toType(val,getGlobalIID(iid)));}
        };

        this.write = function(iid, name, val, lhs, isGlobal, isScriptLocal) {
            
            if(name=='this') {return;}

            var base = "frame " + currentFrame[currentFrame.length-1];
            if(isGlobal||isScriptLocal){base = "frame global";}
            
            if(!val) {collect(base,name,toType(val,sandbox.getGlobalIID(iid)));return;}
            if(getAnnotation(val)) { collect(base,name,toType(val,getGlobalIID(iid))); }
            else if(val.constructor.name == "object") {collect(annotate(base),name,toType(val,getGlobalIID(iid)));}
                 else {collect(base,name,toType(val,getGlobalIID(iid)));}
        };

        this.literal = function(iid,val,hasGetterSetter){

            if(typeof val == 'string') {collectTyAn(getGlobalIID(iid),val);}
            else if(val !== null && typeof val == 'object') {annotate(val);}
        };

        //end of Jalangi2 API functions

        //constraint collection function. Constraints base to have prop with type.
        //Constraints given by user are trusted and should be enforced.
        //base:String, prop:String, type:[String,String,[Number]], trusted:Bool
        function collect(base, prop, type, trusted){
                
            var obs = observations;

            if(debugCollect){console.log([base,prop,type,trusted]);}
            if(trusted){ obs = trustedObservations;}
            if (!obs[base]) {obs[base]=[];}
            if (!obs[base][prop]) {obs[base][prop]=[];}
            if (!obs[base][prop][type[0]]) {obs[base][prop][type[0]]=[type[1],type[2]];}
            else { obs[base][prop][type[0]] = mergeTypes([type[1],type[2]],obs[base][prop][type[0]]);}
        };


        function toType(v,iid){
            switch(typeof v){
                case 'number':
                    return [typeof v,v,[iid]];
                case 'boolean':
                    return [typeof v,v,[iid]];
                case 'string':
                    if(v.length>10){return [typeof v, "T",[iid]];}
                    else {return [typeof v,v,[iid]];}
                    break;
                case 'undefined':
                    return [typeof v,"T",[iid]];
                case 'object':
                    if(v===null) {return ["null","T",[iid]];}
                    else {  
                            if(v.constructor && v.constructor.name == "Array") {return ["Array","T",[iid]];}
                            else    if(iid) {return ["object " + getAnnotation(v),"T",[iid]];}
                                    else {return "object " + getAnnotation(v);}
                    }
                    break;
                case 'function':
                    return [('function '+ getAnnotation(v)), "T" , [iid]];
                default:
                    return [typeof v, "T" , [iid]];
            }
            return [typeof v, "T" , [iid]];
        
        };

        function isNative(fn){return (/\{\s*\[native code\]\s*\}/).test('' + fn);};

        //merge type with list of types
        function mergeTypes(t1, t2){
            var t1v=t1[0];
            var t1i=t1[1];
            var t2v=t2[0];
            var t2i=t2[1];

            if(t1v===t2v){
                return [t1v,mergeArray(t1i,t2i)];
            }
            return ["T",mergeArray(t1i,t2i)];
        };   
        
        function annotate(obj, name){
            if(obj.shadow!== undefined){return obj;}
            if(obj.constructor && obj.constructor.name == "Array") {return obj;}
            if(typeof obj == 'object' || typeof obj == 'function'){
                var annName = "";
                if(name) {annName=name;}
                else if(obj.name) {annName=obj.name;}
                     else {annName = count; count++;}
                    
                Object.defineProperty(obj,'shadow',{
                    enumerable: false,
                    writable: false,
                    value: annName
                    });
                    count++;
            }
            return obj;
        };

        function getAnnotation(obj){
            if(obj.shadow===undefined){annotate(obj);}
            return obj.shadow;
        };

        function lexT(type){
            var cnt=1;
            var index =0;
            //this function parses the type part of an annotation
            //it returns a nested array, representing the types
            //every array has a first element indicating if it is an object (o) or function (f)
            if(type.length === 0) {return [];}
            if(type[0]==='['){
                //find closing bracket
                while(cnt>0){
                    index++;
                    if(type[index]=== '['){cnt++;}
                    else if (type[index] === ']'){cnt--;}
                }
                //if we leave the loop, we have our closing bracket
                return [["o"].concat(lexObj(type.substr(1,index-1)))];
 
            }
            else if (type[0] === '{'){
                //find closing curly bracket
                while(cnt>0){
                    index++;
                    if(type[index]=== '{'){cnt++;}
                    else if (type[index] === '}'){cnt--;}
                }
                //if we leave the loop, we have our closing bracket
                return [["f"].concat(lexFun(type.substr(1,index-1)))];
            }
            else if (type == "number"){
                return ['number'];
            }
            else if (type ==  "boolean"){
                return ['boolean'];
            }
            else if (type == "string"){
                return ['string'];
            }
            else if (type == "undefined"){
                return ['undefined'];
            }
            else if (type == "()"){
                return ['undefined'];
            }
            else if (type == "Array"){
                return ['Array'];
            }
            else if (type == "self"){
                return ['self'];
            }
            else if (type == "?"){
                return ['?'];
            }
            else if (type == "null"){
                return ['null'];
            }
            else if (type.indexOf("|")!== -1){
                cnt = 0;
                while(index<type.length){
                    index++;
                    if(type[index]=== '{'||type[index]==='['){cnt++;}
                    else if (type[index] === '}'||type[index]===']'){cnt--;}
                    else if (type[index] === '|' && cnt === 0){
                        break;
                    }
                }
                var ret = lexT(type.substr(0,index));
                console.log(ret,index);
                return ret.concat(lexT(type.substr(index+1)));
                
            }
            else {console.log("ERROR: Could not lex type. Input remaining: " + type);}

        }

        function lexFun(type){
            //console.log("lexFun called with " + type);
            var cnt = 0; //levelcounter
            var index = 0; //indexcounter
            var result = [];

            while(type[index]){
                if(type[index]==="{"||type[index]==="["){cnt++;}
                else if(type[index]==="}"||type[index]==="]"){cnt--;}
                else if(cnt===0&&type.substr(index,2)=="->"){
                    //console.log(type.substr(0,index));
                    result = result.concat([lexT(type.substr(0,index))]);
                    //console.log(result);
                    type = type.substr(index+2);
                    index = -1;
                }
                index++;
            }
            //console.log(result);
            return result.concat([lexT(type)]);
        }

        function lexObj(type){
            //we know that we have on object type
            //first, we split on ",", but only if we are not inside a subtype
            //then, we build the components

            var cnt = 0; //levelcounter
            var index = 0; //indexcounter
            var splittypes = [];
            var result = [];

            while(type[index]){
                if(type[index]==="{"||type[index]==="["){cnt++;}
                else if(type[index]==="}"||type[index]==="]"){cnt--;}
                else if(cnt===0 && type[index]===","){
                    splittypes.push(type.substr(0,index));
                    type = type.substr(index+1);
                    index = 0;
                }
                index++;
            }
            splittypes.push(type);
            //we now have the object types
            for(var index in splittypes){
                cnt = splittypes[index].indexOf(':');
                result.push([splittypes[index].substr(0,cnt)].concat([lexT(splittypes[index].substr(cnt+1))]));
            }
            //console.log(result);
            return result;
        }


        function parseObjType(type,iid,o){
            //if we arrive here, we have either an obj type ([x:t,y:t,z:t) or function type ({t->t->t)
            //console.log(type,iid,o);
            if(type[0]=="o"){
                //console.log("object type detected");
                for(var i=1; i<type.length; i++){ //for every property
                    for(var it=0; it<type[i][1].length; it++){ //for every type of this property

                    if(false){ //((type[i][it][0]=="o"||type[i][it][0]=="f")&&type[i][it][0].length == 1){
                        //console.log("recursing on " + type[i][0]);
                        var currentCount = count;
                        count++;
                        parseObjType(type[i],iid,"object "+currentCount);
                        collect(o,type[i][0],["object "+currentCount,"T",[iid]],true);
     
                        
                    }
                    else{
                        
                           
                                if(type[i][1][it][0]=="o"||type[i][1][it][0]=="f"){
                                //console.log("recursing on " + type[i][0]);
                                var currentCount = count;
                                count++;
                                parseObjType(type[i][1][it],iid,"object "+currentCount);
                                collect(o,type[i][0],["object "+currentCount,"T",[iid]],true);
    
                            }
                            else {
                                //in this case, we just process the base types
                                collect(o,type[i][0],[type[i][1][it],"T",[iid]],true); //we need to check for recursion here too!
                            
                            }
                            
                        
                    }
                }
                }
                //console.log("done processing object type");
            }
            else if(type[0]=="f"){
                //console.log("function type detected");

                for(var i=1; i<type.length; i++){
                    for(var tyindex in type[i]){
                    if((type[i][tyindex][0]=="o"||type[i][tyindex][0]=="f")&&type[i][tyindex][0].length == 1){
                        //console.log("recursing: "+type[i][0]);
                        var currentCount = count;
                        count++;
                        parseObjType(type[i][tyindex],iid,"object "+currentCount);
                        if(i==type.length-1){collect(o,"return",["object "+currentCount,"T",iid],true);}
                        else{collect(o,"arg"+(i-1),["object "+currentCount,"T",[iid]],true);}
                        
                    }
                    else{
                        //in this case, we just process the base types
                        if(i==type.length-1){collect(o,"return",[type[i][tyindex],"T",[iid]],true);}
                        else{collect(o,"arg"+(i-1),[type[i][tyindex],"T",[iid]],true);}
                    }
                }
            }
            }
            else {console.log("ERROR: Could not parse " + type);}
        };

        function collectTyAn(iid,tyAn){
            var basekind = false;

            if(tyAn.substring(0,8)=="function" && tyAn[tyAn.length-1]=="}"){ basekind = "function";}
            else if (tyAn.substring(0,5)=="frame" && tyAn[tyAn.length-1]=="]") { basekind = "frame";}
            if(basekind){
                //we detected a trusted function type annotation
                if(observedAnnotations[tyAn]){return;}else{observedAnnotations[tyAn]=true;} //prevent annotations from begin analysed every time
                
                var types = lexT(tyAn.substr(tyAn.indexOf(':')+1))[0];
                           
                if(basekind == "function"){
                    var base = tyAn.substr(0,tyAn.indexOf(':'));  //extract what is to be typed
                    collect("frame " + currentFrame[currentFrame.length-1],base.substr(basekind.length+1),[base,"T",[iid]],true); //constrain current frame to contain this
                
                    parseObjType(types,iid,base);   //constrain the return type               
                    
                }
                if(basekind == "frame"){parseObjType(types,iid,"frame " + currentFrame[currentFrame.length-1]);}                            
            }
        };

        function isSubtype(sub,sup){
            if(sub === undefined || sup === undefined) {return false;}
            //we want to establish if sub is a subtype of sup
            for(var prop in sub){              
                if (!sup[prop]) {return false;}
                for(var type in sub[prop]){                 
                    var present = false;
                    for(var type2 in sup[prop]){if (type===type2) {present = true;}}
                    if(!present) {return false;}               
                }
            }
            return true;
        }

        function mergeArray(a,b){
            if(!b){return a;}
            else {  var c = a.concat(b.filter(function (item){return a.indexOf(item)<0;}));
                    return c;
            }
        }


        //This function removes duplicate row (object) types.
        //Takes a list, indexed with "base"
        function remDupRowtypes(types,trustedTypes){
            var substMap = [];  //this variable holds our substitution
            var hashmap = [];

            for (var base in types){

                var isGeneric = (/^function\ ?[0-9]*$|^object\ ?[0-9]*$|^frame\ [0-9]*$/).test(base);
                var hash = "";
                var propHash = [];

                for(prop in types[base]){
                    var pHash = "";
                    pHash+=prop;
                    var tHash = []
                    for(var type in types[base][prop]){
                            //while were here, we might as well check for recursive types
                            //if a type is equal to its base, we replace it with the keyword "self"
                            if(type==base){ types[base][prop]["self"]=types[base][prop][type];
                                            delete types[base][prop][type];
                                            tHash.push("self");}
                            else {tHash.push(type);}
                        }
                    tHash.sort();
                    pHash+=tHash.join();
                    propHash.push(pHash);
                }
                propHash.sort();
                hash = propHash.join();
                //console.log(hash);
                if(!hashmap[hash]){hashmap[hash]=base;}
                else {
                    if(isGeneric){
                        substMap[base]=hashmap[hash];
                        delete types[base];
                    }
                    else{
                        //in this case, we are not generic, and need to perserve
                        var substGeneric = (/^function\ ?[0-9]*$|^object\ ?[0-9]*$|^frame\ [0-9]*$/).test(hashmap[hash]);
                        if(substGeneric){
                            //in this case, what we substitute to is generic. In this case, we switch it around!
                            substMap[hashmap[hash]] = base;
                            hashmap[hash]=base;
                        }
                        else{
                            //in this case, what we substitute to is not generic. But since we are not generic too, we do nothing
                        }
                    }       
                }
            }       
            //console.log(substMap);
            for (base in trustedTypes){
                var isGeneric = (/^function\ ?[0-9]*$|^object\ ?[0-9]*$|^frame\ [0-9]*$/).test(base);
                var hasht = "";
                propHash = [];
                for(var propt in trustedTypes[base]){
                    pHash = "";
                    pHash+=propt;
                    tHash = []
                    for(var typet in trustedTypes[base][propt]){tHash.push(typet);}
                    tHash.sort();
                    pHash+=tHash.join();
                    propHash.push(pHash);
                }
            propHash.sort();
            hasht = propHash.join();
            //console.log(hasht);

                if(!hashmap[hasht]){hashmap[hasht]=base;}
                else {
                    if(isGeneric){
                        substMap[base]=hashmap[hasht];
                        delete trustedTypes[base];
                    }
                    else{
                        //in this case, we are not generic, need to preserve

                        var substGeneric = (/^function\ ?[0-9]*$|^object\ ?[0-9]*$|^frame\ [0-9]*$/).test(hashmap[hasht]);
                        if(substGeneric){
                            //in this case, we substitute to generic, so switch around
                            substMap[hashmap[hasht]] = base;
                            hashmap[hasht]=base;   //watch out, is this a safe operation?
                        }
                        else{
                            //in this case, we do not substitute, since both are not generic.
                        }
                    }
                }
                }
            
            
            //console.log(substMap);
            //filter out substitutions that refer to substituted objects
            for (var i in substMap){if(substMap[substMap[i]]){substMap[i] = substMap[substMap[i]];}}
            //run trough the types and apply substitution
            function appSubst (types) {
                for (base in types){
                for (var prop in types[base]){
                    for (var typename in types[base][prop]){
                        if(substMap[typename]) {

                            //retrieve type info from current typename
                            var currentTypeinfo = types[base][prop][typename];


                            //if new type name is present, then merge

                            var newTypeinfo = types[base][prop][substMap[typename]];
                            if(newTypeinfo){
                                types[base][prop][substMap[typename]]=mergeTypes(newTypeinfo,currentTypeinfo);
                            }

                            //else just store the type information under new type name

                            else{types[base][prop][substMap[typename]]=currentTypeinfo;}

                            //remove old typename
                            delete types[base][prop][typename];

                            //done

                            
                            }
                        }
                    }
                }
            }
            appSubst(types);
            appSubst(trustedTypes);
        }


        function checkTrustedTypes(trusted,observed){
            var errors = [];
            //this function currently does not account for object (row) types.

            //for every annotated thing
            for (var base in trusted){

                //if it does not occur in the observations -> error
                if(!observed[base]) {errors.push(base + " not observed"); continue;}

                //for every property of the annotated thing
                for(var prop in trusted[base]){

                    //if the property is not observed -> error
                    if(!observed[base][prop]) {errors.push(prop + " not observed in " + base); continue;}

                    //otherwise we collect the types of trusted and observed

                    var tylistt = [];
                    var tylisto = [];
                    for (var index in trusted[base][prop]){tylistt.push(index);}
                    for (var oIndex in observed[base][prop]){tylisto.push(oIndex);}

                    //now we compare the two lists
                    //first, we check all basic types
                    tylisto = tylisto.filter( function( el ) {return tylistt.indexOf( el ) < 0;} );
                    //now, only different types and type variables remain
                    tylisto = tylisto.filter( function( el ) {return (tylistt.map(function(eltrust){return isSubtype(trusted[eltrust],observed[el])})).indexOf(true)<0;} );

                    //if(tylisto.length>0){
                     //   for(var tyli in tylisto){
                       // var loc = "";
                     //   for (var iidindex in trusted[base][prop][tylisto[tyli]][1]){
                     //   loc += prettyPrintIID(trusted[base][prop][tylisto[tyli]][1][iidindex]);}
                     //   errors.push("Observed type of "+prop+" in "+base+": "+tylistt+" \n\tis different from annotated type: " + tylisto[tyli] +" declared at "+loc);
                     //  }     
                  //}
                  if(tylisto.length>0){


                    errors.push("Observed type for "+prop+" in "+base+": "+tylisto+" \n\tis different from annotated type: " + tylistt +" decalred at ?????");}
                        }
                    
                
            }
            return errors;
        }

        function typeDifference(typelist,observed){
            var result = 0;
            var head = typelist.shift();

            for (var type in typelist){
                for (var prop in observed[type]){
                    if (!observed[head][prop]) {result++;}
                }
            }
            return (result);
        }

        function checkTypeInconsistence(observed){
            var warnings = [];

            for (var base in observed){
                for (var prop in observed[base]){  
                    var c = 0;
                    var obstypes = "";
                    var typelist = [];
                    for (var type in observed[base][prop]){
                        if(pruneNullInc && type==="null"){continue;}  //prune null warnings
                        typelist.push(type);
                        var loc = "";
                        var i = 0;
                        if(condenseReports){
                                loc += prettyPrintIID(observed[base][prop][type][1][0]);
                                if((i=observed[base][prop][type][1].length)>1) {loc += " and " + i + " more location(s)";}
                        }
                        else {  for (var iidindex in observed[base][prop][type][1]){
                                    if (i) {loc+=" and ";}
                                    loc += prettyPrintIID(observed[base][prop][type][1][iidindex]);
                                    i++;
                                }
                        }
                        obstypes+="\t"+prettyPrintType(type,observed[base][prop][type][0])+"at "+ loc + "\n";
                        c ++;
                    }
                    if(c>1&&c<=pruneTypeCount){warnings.push("Property " + prop + " in "+ base + " has inconsistent type:\n" + obstypes );}
                }
            }
            return warnings;
        }

        function prettyPrintIID(iid){

            var res = iidToLocation(iid);
            res = res.substr(res.indexOf(":")+1);
            res = res.substr(0,res.length-1);

            return res;

        }

        function prettyPrintType(name,value){

            var composedTypes = ['number','boolean','string'];
            if(composedTypes.indexOf(name)>=0){return name+"("+value+") ";}
            else {return name+" ";}
        }

        function prettyPrintTypes(types){

            var res = "";

            for (var base in types){
                if(base.substr(0,8)==="function"){
                    res+= base + " has the following type:\n\t";
                    var c = 0;
                    while (types[base]["arg"+c]){
                        if(c!==0) {res+="-> ";}
                        res+="arg"+c+ " ";
                        for(var index in types[base]["arg"+c]) {res+=prettyPrintType(index,types[base]["arg"+c][index][0]);}
                        c++;
                    }
                    if(c!==0) res+="-> ";
                    res+="return ";
                    for(var i in types[base]["return"]) {res+=prettyPrintType(i,types[base]["return"][i][0]);}
                    res+="\n";
                }
                else{
                    res+= base + " has the following properties:\n";
                    for(var prop in types[base]){
                        res+="\t" + prop + " with type: ";
                        for(var idx in types[base][prop]) {res+=prettyPrintType(idx,types[base][prop][idx][0]);}
                        res+="\n";
                    }
                } 
            }
            return res;
        }


        this.endExecution = function() {
         
            console.log("Program execution completed...");
            //console.log(trustedObservations);
            if(timeExecution){console.time("remDups");}
            remDupRowtypes(observations,trustedObservations);
            remDupRowtypes(observations,trustedObservations);
            if(timeExecution){console.timeEnd("remDups");}
            console.log(trustedObservations);
            
            if(printWarnings){
                if(timeExecution){console.time("genErrors");}
                var errors = checkTrustedTypes(trustedObservations,observations);
                console.log("We detected " + errors.length + " type error(s)\n");
                if(errors){ for (var index in errors){console.log(errors[index]);}
                            console.log();}
                if(timeExecution){console.timeEnd("genErrors");}
            }

            if(printErrors){
                if(timeExecution){console.time("genWarnings");}
                var warnings = checkTypeInconsistence(observations);
                console.log("We detected " + warnings.length + " type warning(s)\n");
                if(warnings){ for (var i in warnings){console.log(warnings[i]);}}
                if(timeExecution){console.timeEnd("genWarnings");}
            }

            if(printTypes){
                console.log("We inferred the following types:\n");
                var vis = prettyPrintTypes(observations);
                console.log(vis);
            }   

            if(timeExecution){console.timeEnd("total");}
        };
    }
    sandbox.analysis = new MyAnalysis();
})(J$);