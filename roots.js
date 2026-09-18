/* MGP snapshot, 17 September 2026. No network requests required. */
(()=>{'use strict';
const D=window.GENEALOGY,ROOT='322229', $=id=>document.getElementById(id);
const name=id=>({'298616':'Ibn Sina (Avicenna)','295739':'Omar Khayyam'}[id]||D[id].name);
const persian={'298616':'ابن‌سینا','295739':'عمر خیام','217509':'خواجه نصیرالدین طوسی'};
const notes={
'298616':['Developed an influential account of logic, including theories of inference and demonstration.','https://plato.stanford.edu/entries/ibn-sina-logic/'],
'295739':['Studied cubic equations through geometric constructions involving conic sections.','https://mathshistory.st-andrews.ac.uk/Biographies/Khayyam/'],
'217509':['Made major contributions to trigonometry and mathematical astronomy.','https://mathshistory.st-andrews.ac.uk/Biographies/Al-Tusi_Nasir/'],
'8011':['Introduced the lambda calculus, a foundational formalism for the study of computation.','https://plato.stanford.edu/entries/lambda-calculus/']};
const fold=s=>s.normalize('NFD').replace(/[\u0300-\u036f]/g,'').replace(/ł/g,'l').replace(/Ł/g,'L').replace(/[يى]/g,'ی').replace(/ك/g,'ک').replace(/\u200c/g,'').toLowerCase();
function showRoute(id){const route=shortest(id);$('connection-path').innerHTML=`<h2>Follow this connection</h2><p class="small">${route.length-1} recorded connections from Ali Farjami to ${esc(name(id))}. One shortest route in the MGP snapshot; historical links are not necessarily doctoral supervision.</p><ol>${route.map((item,i)=>`<li><button data-route="${item}" ${item===id?'aria-current="true"':''}>${esc(name(item))}</button>${i && special.has(route[i-1])?'<span class="small"> — intellectual heritage / correspondence link</span>':''}</li>`).join('')}</ol>`;document.querySelectorAll('[data-route]').forEach(b=>b.onclick=()=>reveal(b.dataset.route));}
let expanded=new Set([ROOT]),selected=ROOT,scope=ROOT,zoom=1,path=[];
const special=new Set(['143011','17864']);
const portrait={
'295739':{file:'khayyam.png',credit:'Omar Khayyam: later artistic interpretation by Adelaide Hanscom for the Rubáiyát, not a contemporary likeness. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Volto_Khayyam.png',license:'Public domain in the United States (Commons designation)'},
'217509':{file:'tusi.jpg',credit:'Khwāja Nasir al-Din Tusi: imagined depiction derived from a 2001 Azerbaijani stamp; derivative by Michel Bakni, 2021. Not a contemporary likeness. Oval presentation; this adaptation is also CC BY-SA 4.0.',url:'https://commons.wikimedia.org/wiki/File:Nasir_al-Din_al-Tusi_portrait.jpg',license:'CC BY-SA 4.0',licenseURL:'https://creativecommons.org/licenses/by-sa/4.0/'},
'8011':{file:'church.png',credit:'Alonzo Church, undated photograph, photographer unknown. Alonzo Church Papers, Princeton University Library. © Princeton University, via Open Logic Project. Included for local preview; permission for public website reuse has not been verified. Displayed in an oval crop.',url:'https://builds.openlogicproject.org/assets/photos/photos.pdf',license:'Restricted reuse — see source credits'},
'108295':{file:'laplace.jpg',credit:'Pierre-Simon Laplace, Jean-Baptiste Paulin Guérin, 1838. Versailles. Posthumous portrait. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Pierre-Simon_Laplace.jpg',license:'Public domain'},
'17865':{file:'poisson.jpg',credit:'Siméon Denis Poisson, lithograph by François-Séraphin Delpech after Nicolas Eustache Maurin, before 1840. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Sim%C3%A9onDenisPoisson.jpg',license:'Public domain'},
'53410':{file:'johann-bernoulli.jpg',credit:'Johann Bernoulli, mezzotint by Johann Jakob Haid after Johann Rudolf Huber, 1742. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Johann_Bernoulli.jpg',license:'Public domain'},
'126177':{file:'copernicus.jpg',credit:'Nicolaus Copernicus, anonymous Toruń portrait, about 1580. District Museum in Toruń. Later depiction, not a lifetime portrait. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Nikolaus_Kopernikus.jpg',license:'Public domain'},
'13105':{file:'boltzmann.jpg',credit:'Ludwig Boltzmann, photograph dated 1902; photographer unknown. Wikimedia Commons version restored by Adam Cuerden. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Boltzmann2.jpg',license:'Public domain in the United States (Commons designation)'},
'17864':{file:'lagrange.jpg',credit:'Joseph-Louis Lagrange, historical portrait; artist and date unrecorded on the source page. Via MacTutor and Wikimedia Commons. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Joseph-Louis_Lagrange.jpeg',license:'Public domain'},
'134975':{file:'galileo.jpg',credit:'Galileo Galilei, Justus Sustermans, 1636. Uffizi; Web Gallery of Art. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Justus_Sustermans_-_Portrait_of_Galileo_Galilei_-_WGA21972.jpg',license:'Public domain'},
'60985':{file:'leibniz.jpg',credit:'Gottfried Wilhelm Leibniz, Christoph Bernhard Francke, about 1695. Herzog Anton Ulrich Museum; museum photograph by Claus Cordes. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Christoph_Bernhard_Francke_-_Bildnis_des_Philosophen_Leibniz_(ca._1695).jpg',license:'Public domain'},
'298616':{file:'ibn-sina.jpg',credit:'Anonymous engraving; later depiction, not a contemporary likeness. Wellcome Library, London. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Portrait_of_Avicenna;_anon.,_Wellcome_M0009341.jpg',license:'CC BY 4.0',licenseURL:'https://creativecommons.org/licenses/by/4.0/'},
'38586':{file:'euler.jpg',credit:'Leonhard Euler, Jakob Emanuel Handmann, 1753. Kunstmuseum Basel. Displayed in an oval crop.',url:'https://commons.wikimedia.org/wiki/File:Leonhard_Euler.jpg',license:'Public domain'}
};
const esc=s=>String(s||'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function shortest(target){let q=[[ROOT]],seen=new Set([ROOT]);for(let i=0;i<q.length;i++){let p=q[i],id=p[p.length-1];if(id===target)return p;for(const a of D[id].advisors)if(!seen.has(a.id)){seen.add(a.id);q.push([...p,a.id]);}}return [];}
function showPerson(id){selected=id;const d=D[id],p=portrait[id];$('person').innerHTML=`${p?`<img class="portrait" src="assets/${p.file}" alt="Historical depiction of ${esc(name(id))}">`:''}<p class="eyebrow">IN THE LINEAGE</p><h2>${esc(name(id))}</h2>${name(id)!==d.name?`<p class="small">${esc(d.name)}</p>`:''}<p>${esc(d.degree||'No degree information recorded.')}</p>${d.thesis?`<p class="small">${special.has(id)?'Source note':'Record / thesis'}: ${esc(d.thesis)}</p>`:''}<p><a href="${d.source}" target="_blank" rel="noopener">Read the MGP record ↗</a></p>${d.advisors.length?`<button class="expand" id="toggle-person">${expanded.has(id)?'Collapse':'Expand'} this branch (${d.advisors.length})</button><h3>Recorded advisors / teachers</h3><ul>${d.advisors.map(a=>`<li><button data-person="${a.id}">${esc(name(a.id))}</button></li>`).join('')}</ul>`:'<p class="small">No advisor is listed in this snapshot. This is a gap in the record, not necessarily the beginning of the tradition.</p>'}${/unknown/i.test(d.notes)?'<p class="small">The source includes an unknown-advisor note; this record may be incomplete.</p>':''}${p?`<p class="credits">${p.credit} <a href="${p.url}">Image source</a> · ${p.licenseURL?`<a href="${p.licenseURL}">${p.license}</a>`:p.license}</p>`:''}`;
if(persian[id])$('person').insertAdjacentHTML('afterbegin',`<p class="persian-name" lang="fa" dir="rtl">${persian[id]}</p>`);
if(notes[id])$('person').insertAdjacentHTML('beforeend',`<section class="contribution"><h3>A contribution</h3><p>${notes[id][0]}</p><a href="${notes[id][1]}" target="_blank" rel="noopener">Read more ↗</a></section>`);
showRoute(id);
document.querySelectorAll('[data-person]').forEach(b=>b.onclick=()=>reveal(b.dataset.person));
if($('toggle-person'))$('toggle-person').onclick=()=>{expanded.has(id)?expanded.delete(id):expanded.add(id);render();showPerson(id);};}
function visible(){let seen=new Set(),edges=[];function visit(id){if(seen.has(id))return;seen.add(id);if(expanded.has(id))for(const a of D[id].advisors){edges.push([id,a.id]);visit(a.id);}}visit(ROOT);if(scope!==ROOT){seen=new Set();edges=[];visit(scope);seen.add(ROOT);edges.unshift([ROOT,scope]);}return {ids:[...seen],edges};}
function render(){const {ids,edges}=visible(),rank=Object.fromEntries(ids.map(id=>[id,0]));for(let n=0;n<ids.length;n++){let changed=false;for(const [a,b]of edges)if(rank[b]<rank[a]+1){rank[b]=rank[a]+1;changed=true;}if(!changed)break;}
const levels=[];for(const id of ids)(levels[rank[id]]??=[]).push(id);
// Measure natural card heights before positioning, including long names and browser text scaling.
$('graph').innerHTML=ids.map(id=>`<button class="root-node ${path.includes(id)?'on-path':''}" id="node-${id}" aria-pressed="${id===selected}" title="${esc(D[id].name)}">${portrait[id]?`<img class="node-portrait" src="assets/${portrait[id].file}" alt="" width="44" height="56">`:''}<span class="node-name">${esc(name(id))}</span><span class="node-status">${D[id].advisors.length?(expanded.has(id)?'− Branch open':'＋ '+D[id].advisors.length+' recorded advisors'):'End of recorded branch'}</span></button>`).join('');
const heights=Object.fromEntries(ids.map(id=>[id,$('node-'+id).offsetHeight]));
const totals=levels.map(list=>list.reduce((h,id)=>h+heights[id]+28,0));
const height=Math.max(500,...totals.map(h=>h+50)),width=levels.length*330+30,pos={};
levels.forEach((list,col)=>{let y=(height-totals[col])/2;list.forEach(id=>{pos[id]={x:25+col*330,y};const b=$('node-'+id);b.style.left=pos[id].x+'px';b.style.top=y+'px';y+=heights[id]+28;});});
const traced=new Set(path.slice(1).map((id,i)=>path[i]+'-'+id));
$('graph').style.width=width+'px';$('graph').style.height=height+'px';$('graph').style.transform=`scale(${zoom})`;$('graph-size').style.width=width*zoom+'px';$('graph-size').style.height=height*zoom+'px';
$('graph').insertAdjacentHTML('afterbegin',`<svg width="${width}" height="${height}" aria-hidden="true">${edges.map(([a,b])=>{const s=pos[a],t=pos[b],sy=s.y+heights[a]/2,ty=t.y+heights[b]/2;return `<path class="${traced.has(a+'-'+b)?'trace ':''}${special.has(a)?'heritage':''}" d="M${s.x+270},${sy} C${s.x+300},${sy} ${t.x-30},${ty} ${t.x},${ty}"/>`;}).join('')}</svg>`);
for(const id of ids)$('node-'+id).onclick=()=>{selected=id;path=shortest(id);render();showPerson(id);$('node-'+id).focus({preventScroll:true});};
$('graph-status').textContent=`${ids.length} of ${Object.keys(D).length} people visible · ${edges.length} connections · ${Math.round(zoom*100)}% zoom. Select a person, then expand their branch. Scroll the canvas to explore.`;
}
function reveal(id){scope=ROOT;$('branch').value=ROOT;path=shortest(id);path.slice(0,-1).forEach(x=>expanded.add(x));selected=id;render();showPerson(id);const b=$('node-'+id);if(b){$('viewport').scrollTo({left:Math.max(0,parseFloat(b.style.left)*zoom-70),top:Math.max(0,parseFloat(b.style.top)*zoom-130),behavior:'instant'});}}
$('search').oninput=()=>{const q=fold($('search').value.trim());const found=q?Object.keys(D).filter(id=>fold(D[id].name+' '+name(id)+' '+(persian[id]||'')).includes(q)):[];$('results').innerHTML=found.map(id=>`<button data-result="${id}">${esc(name(id))}</button>`).join('');$('search-status').textContent=q?`${found.length} matches in the full genealogy`:'';document.querySelectorAll('[data-result]').forEach(b=>b.onclick=()=>reveal(b.dataset.result));};
$('branch').onchange=()=>{scope=$('branch').value;expanded.add(ROOT);expanded.add(scope);path=[];selected=scope;render();showPerson(scope);$('viewport').scrollTo(0,0);};
$('show-all').onclick=()=>{expanded=new Set(Object.keys(D));render();showPerson(selected);};
$('reset').onclick=()=>{expanded=new Set([ROOT]);scope=ROOT;selected=ROOT;path=[];zoom=1;$('branch').value=ROOT;$('search').value='';$('results').innerHTML='';$('search-status').textContent='';render();showPerson(ROOT);$('viewport').scrollTo(0,0);};
$('zoom-in').onclick=()=>{zoom=Math.min(1.6,zoom+.15);render();};$('zoom-out').onclick=()=>{zoom=Math.max(.85,zoom-.15);render();};
document.querySelectorAll('[data-trace]').forEach(b=>b.onclick=()=>reveal(b.dataset.trace));
render();showPerson(ROOT);
const requested=new URLSearchParams(window.location.search).get('person');
if(requested && Object.prototype.hasOwnProperty.call(D,requested))reveal(requested);
})();
