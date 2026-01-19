import { useState, useEffect } from 'react';
import { Container, Row, Col, Form, Button, ListGroup, Badge, ButtonGroup } from 'react-bootstrap';
import { FaTrash, FaCheck, FaPlus } from 'react-icons/fa';
import type { Todo } from './types';
import './App.css';

function App() {
  const [todos, setTodos] = useState<Todo[]>(() => {
    const saved = localStorage.getItem('todo-app-data');
    if (saved) {
      try {
        return JSON.parse(saved);
      } catch (e) {
        console.error("Failed to parse todos", e);
        return [];
      }
    }
    return [];
  });
  const [inputValue, setInputValue] = useState('');
  const [filter, setFilter] = useState<'all' | 'active' | 'completed'>('all');

  useEffect(() => {
    localStorage.setItem('todo-app-data', JSON.stringify(todos));
  }, [todos]);

  const handleAddTodo = (e: React.FormEvent) => {
    e.preventDefault();
    if (!inputValue.trim()) return;

    const newTodo: Todo = {
      id: crypto.randomUUID(),
      text: inputValue.trim(),
      completed: false,
      createdAt: Date.now(),
    };

    setTodos([newTodo, ...todos]);
    setInputValue('');
  };

  const toggleTodo = (id: string) => {
    setTodos(todos.map(todo => 
      todo.id === id ? { ...todo, completed: !todo.completed } : todo
    ));
  };

  const deleteTodo = (id: string) => {
    setTodos(todos.filter(todo => todo.id !== id));
  };

  const filteredTodos = todos.filter(todo => {
    if (filter === 'active') return !todo.completed;
    if (filter === 'completed') return todo.completed;
    return true;
  });

  const activeCount = todos.filter(t => !t.completed).length;

  return (
    <Container className="py-5" style={{ maxWidth: '600px' }}>
      <Row className="mb-4 text-center">
        <Col>
          <h1 className="display-4 fw-bold text-primary">Todo List</h1>
          <p className="text-muted">Stay organized and productive</p>
        </Col>
      </Row>

      <Row className="mb-4">
        <Col>
          <Form onSubmit={handleAddTodo}>
            <div className="d-flex gap-2">
              <Form.Control
                type="text"
                placeholder="What needs to be done?"
                value={inputValue}
                onChange={(e) => setInputValue(e.target.value)}
                size="lg"
                className="shadow-sm"
              />
              <Button variant="primary" type="submit" size="lg" className="px-4 shadow-sm" disabled={!inputValue.trim()}>
                <FaPlus />
              </Button>
            </div>
          </Form>
        </Col>
      </Row>

      <Row className="mb-3">
        <Col className="d-flex justify-content-between align-items-center">
          <ButtonGroup>
            <Button 
              variant={filter === 'all' ? 'primary' : 'outline-primary'} 
              onClick={() => setFilter('all')}
              size="sm"
            >
              All
            </Button>
            <Button 
              variant={filter === 'active' ? 'primary' : 'outline-primary'} 
              onClick={() => setFilter('active')}
              size="sm"
            >
              Active
            </Button>
            <Button 
              variant={filter === 'completed' ? 'primary' : 'outline-primary'} 
              onClick={() => setFilter('completed')}
              size="sm"
            >
              Completed
            </Button>
          </ButtonGroup>
          <Badge bg="secondary" className="p-2">
            {activeCount} items left
          </Badge>
        </Col>
      </Row>

      <Row>
        <Col>
          <ListGroup variant="flush" className="shadow-sm rounded overflow-hidden">
            {filteredTodos.length === 0 ? (
              <ListGroup.Item className="p-5 text-center text-muted bg-light">
                {filter === 'all' && todos.length === 0 
                  ? "No tasks yet. Add one above!" 
                  : `No ${filter} tasks found.`}
              </ListGroup.Item>
            ) : (
              filteredTodos.map(todo => (
                <ListGroup.Item 
                  key={todo.id}
                  className={`d-flex align-items-center p-3 border-bottom ${todo.completed ? 'bg-light' : ''}`}
                  action
                  onClick={() => toggleTodo(todo.id)}
                  style={{ cursor: 'pointer', transition: 'background-color 0.2s' }}
                >
                  <div 
                    className={`rounded-circle d-flex align-items-center justify-content-center me-3 border ${todo.completed ? 'bg-success border-success' : 'border-secondary'}`}
                    style={{ width: '24px', height: '24px', minWidth: '24px' }}
                  >
                    {todo.completed && <FaCheck color="white" size={12} />}
                  </div>
                  
                  <span 
                    className={`flex-grow-1 ${todo.completed ? 'text-decoration-line-through text-muted' : ''}`}
                    style={{ fontSize: '1.1rem' }}
                  >
                    {todo.text}
                  </span>

                  <Button 
                    variant="outline-danger" 
                    size="sm" 
                    className="ms-2 opacity-50 hover-opacity-100 delete-btn"
                    onClick={(e) => {
                      e.stopPropagation();
                      deleteTodo(todo.id);
                    }}
                    title="Delete task"
                  >
                    <FaTrash />
                  </Button>
                </ListGroup.Item>
              ))
            )}
          </ListGroup>
        </Col>
      </Row>
    </Container>
  );
}

export default App;