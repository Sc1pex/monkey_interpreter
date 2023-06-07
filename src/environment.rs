use crate::object::Object;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub type Env = Rc<RefCell<Environment>>;

#[derive(Debug, PartialEq, Clone, Default)]
pub struct Environment {
    store: HashMap<String, Object>,
    outer: Option<Env>,
}

impl Environment {
    pub fn new_enclosed(outer: &Env) -> Self {
        Self {
            store: HashMap::new(),
            outer: Some(Rc::clone(outer)),
        }
    }

    pub fn get(&self, name: &str) -> Option<Object> {
        self.store.get(name).cloned().or_else(|| {
            self.outer
                .as_ref()
                .and_then(|outer| outer.borrow().get(name))
        })
    }

    pub fn set(&mut self, name: &str, value: Object) {
        self.store.insert(name.into(), value);
    }
}
