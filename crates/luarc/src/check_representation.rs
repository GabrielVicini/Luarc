//! Reject structural type expansion that has no finite generated Rust spelling.

use crate::check::Checker;
use crate::diag::Span;
use crate::types::*;

impl<'a> Checker<'a> {
    pub(crate) fn validate_type_expansion(&mut self) {
        let handles = self.st.tys.len();
        let mut graph = vec![Vec::new(); handles + self.st.tabs.len()];
        for (i, edges) in graph[..handles].iter_mut().enumerate() {
            let mut slots = Vec::new();
            match self.st.node(i as TyId) {
                TyNode::Table(tab) => {
                    let tab = self.st.tab_root(*tab);
                    match self.st.tab(tab).kind {
                        TKind::Array | TKind::Unknown => slots.extend(self.st.tab(tab).elem),
                        TKind::Map => slots.extend(self.st.tab(tab).val),
                        // A generated record name is a nominal boundary; its data fields are not expanded here.
                        TKind::Record => edges.push(handles + tab as usize),
                    }
                }
                TyNode::Func(function) => {
                    slots.extend(&function.params);
                    slots.extend(function.vararg);
                    slots.extend(self.st.rets_known(function.rets).into_iter().flatten());
                    slots.extend(self.st.rets_tail(function.rets));
                }
                TyNode::FalseOr(inner) => edges.push(self.st.root(*inner) as usize),
                TyNode::Pcall(slot) => slots.push(*slot),
                TyNode::Future(results) => slots.extend(results.iter()),
                TyNode::Native(native) => {
                    edges.extend(native.args.iter().map(|ty| self.st.root(*ty) as usize))
                }
                _ => {}
            }
            edges.extend(slots.iter().map(|slot| self.st.root(slot.ty) as usize));
        }
        for (i, tab) in self
            .st
            .tabs
            .iter()
            .enumerate()
            .filter(|(_, tab)| tab.link.is_none())
        {
            if let Some(meta) = tab.metatable {
                graph[handles + i].push(handles + self.st.tab_root(meta) as usize);
            }
        }
        // Generic containers/functions need finite expansion; traverse iteratively so malformed types cannot overflow.
        let mut colors = vec![0; graph.len()];
        for start in 0..graph.len() {
            let mut stack = vec![(start, false)];
            while let Some((node, leaving)) = stack.pop() {
                if leaving {
                    colors[node] = 2;
                    continue;
                }
                if colors[node] == 2 {
                    continue;
                }
                if colors[node] == 1 {
                    let span = if node >= handles {
                        self.st.tab((node - handles) as TabId).span
                    } else if let TyNode::Table(tab) = self.st.node(node as TyId) {
                        self.st.tab(*tab).span
                    } else {
                        self.res
                            .syms
                            .iter()
                            .enumerate()
                            .find_map(|(i, symbol)| {
                                self.info
                                    .sym_slot
                                    .get(&(i as u32))
                                    .filter(|slot| {
                                        self.st.root(slot.ty) == self.st.root(node as TyId)
                                    })
                                    .map(|_| symbol.span)
                            })
                            .unwrap_or(Span::default())
                    };
                    self.error(span, "recursive type expansion is not supported; use a record to break the cycle");
                    return;
                }
                colors[node] = 1;
                stack.push((node, true));
                stack.extend(graph[node].iter().rev().map(|child| (*child, false)));
            }
        }
    }
}
